-- Prove2me | Theorems.Thm_DetDLP_oracle_search_and_scan_tm_compilation
-- name    : DetDLP.oracle_search_and_scan_tm_compilation
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T14:03:05.037109+00:00
-- url     : https://prove2.me/theorems/03d31c9c-abe2-48bd-83ee-fd66e93a7f21
-- title:
--   Unified Multitape Turing-Machine Oracle-Driver Compilation for Divisor Search, Tree Splitting, and Component Scanning
-- statement:
--   Given the proved interval-bisection decision invariant (`DetDLP.divisor_bisection_and_btn_scale`) and the proved linear splitting-tree size and prime-factor list recovery theorem (`DetDLP.splitting_tree_size_and_prime_power_from_factors`), compiles the three polynomial-overhead deterministic multitape Turing-machine oracle drivers of Sections 2.3 and 3.3: (1) the $n$-step interval-bisection BTN driver outputting $\mathrm{minFac}(N)$, (2) the $O(n)$-node tree-splitting and merge-sort driver, and (3) the prime-power component scan driver over the flattened Stage I factor base.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3 Proposition 2.6 & Section 3.3 Proposition 3.3 (pp. 10–11, 14)

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Unified multitape Turing-machine oracle-driver compilation for Section 2.3 (Proposition 2.6)
and Section 3.3 (Proposition 3.3), given the proved interval-bisection invariant
(`DetDLP.divisor_bisection_and_btn_scale`) and the proved polynomial recursion-tree size and
prime-factor list recovery theorem (`DetDLP.splitting_tree_size_and_prime_power_from_factors`). -/
theorem oracle_search_and_scan_tm_compilation :
    ((∀ N : ℕ, 2 ≤ N → ¬ N.Prime → 2 ≤ N.minFac ∧ N.minFac < N ∧ N.minFac ∣ N) ∧
     (∀ N L M R : ℕ, L ≤ M → M ≤ R →
       ((Finset.Ico L R).filter (fun d => d ∣ N)).card =
         ((Finset.Ico L M).filter (fun d => d ∣ N)).card +
         ((Finset.Ico M R).filter (fun d => d ∣ N)).card) ∧
     (∀ N L M R : ℕ, 2 ≤ N → ¬ N.Prime → 2 ≤ L → L ≤ N.minFac → N.minFac < R → L ≤ M → M ≤ R →
       (N.minFac < M ↔ 0 < ((Finset.Ico L M).filter (fun d => d ∣ N)).card) ∧
       (M ≤ N.minFac ↔ ((Finset.Ico L M).filter (fun d => d ∣ N)).card = 0))) →
    ((∀ (f : ℕ → ℕ),
        let split : ℕ → ℕ → List ℕ :=
          Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
            let d := f x
            if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])
        (∀ (k x : ℕ), 2 ≤ x → 1 ≤ (split k x).length ∧ 2 ^ (split k x).length ≤ x) ∧
        (∀ (N : ℕ), 2 ≤ N →
          let n := bitLen (N + 1)
          (split n N).length ≤ n)) ∧
     (∀ (n : ℕ), 1 ≤ n →
        (∀ r : ℕ, r ∈ n.primeFactors ↔ r ∈ n.primeFactorsList) ∧
        n.primeFactorsList.prod = n ∧
        n.primeFactors.card ≤ n.primeFactorsList.length)) →
    ((∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
        ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
          ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
            ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
              (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
              2 ≤ s → G.nE ≤ C * s → G.nV ≤ s ^ c0 →
              G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
              1 ≤ P0 → P0 ≤ C * s → 1 ≤ ℓ → ℓ ≤ C * s →
              BTNEntryEvaluable desc G P0 ℓ T E outE
                (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
                (((s + desc.length : ℕ) : ℝ) ^ c0) →
              ∃ w : List Bool,
                EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
                RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                  (btnTimeBound K (s + desc.length) s)
                  (polyBound K (s + desc.length))) →
      (∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
        ∀ d : ℕ, 1 ≤ d →
          ∃ (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
            (ext : Fin (4 * d) → Fin G.nE),
            G.nE < 1100 * (d + 1) ∧
            (G.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
            (G.nV : ℝ) ≤ polyBound K d ∧
            BoolBTNEntryEvaluable (countWord d) G T E outE (polyBound K d) (polyBound K d) ∧
            IsParsimonious G T ext (fun x =>
              bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
              bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
              bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩))) →
      ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ N : ℕ, 2 ≤ N →
          let n := bitLen (N + 1)
          RunsWithin M out (countWord N) (countWord N.minFac)
            ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) (polyBound K n)) ∧
    (∀ (f : ℕ → ℕ) (Md : PrimitiveMachine) (od : Fin Md.tapeCount) (Kd : ℕ),
      (∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin Md od (countWord N) (countWord (f N))
          ((2 : ℝ) ^ ((Kd : ℝ) * n / Real.sqrt (logSafe n))) (polyBound Kd n)) →
      ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ N : ℕ, 2 ≤ N →
          let n := bitLen (N + 1)
          let split : ℕ → ℕ → List ℕ :=
            Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
              let d := f x
              if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])
          RunsWithin M out (countWord N) (encodeNatListBin ((split n N).mergeSort))
            ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) (polyBound K n)) ∧
    (∀ (Mf : PrimitiveMachine) (ofac : Fin Mf.tapeCount) (Kf : ℕ),
      (∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin Mf ofac (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((Kf : ℝ) * n / Real.sqrt (logSafe n))) (polyBound Kf n)) →
      ∀ (Me : PrimitiveMachine) (oe : Fin Me.tapeCount) (Ke : ℕ),
        ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
          ∀ (p : ℕ) [Fact p.Prime],
            let b := bitLen p
            let m := blockCount b
            ∀ F : Fin m → List (ZMod p)ˣ,
              RunsWithin Me oe (countWord p) (encodeFpFactorBlocks F)
                (mainSpaceBound Ke b) (mainSpaceBound Ke b) →
              let n := p - 1
              let U := (List.ofFn F).flatten
              let h : (ZMod p)ˣ := ∏ r ∈ n.primeFactors,
                ((U.find? (fun u => decide (u ^ (n / r) ≠ 1))).getD 1) ^ (n / r ^ (n.factorization r))
              RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
                (mainSpaceBound C b) (mainSpaceBound C b)) := by sorry

end DetDLP
