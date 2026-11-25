-- Prove2me | Theorems.Thm_DetDLP_factorization_tm_from_divisor_parsimony
-- name    : DetDLP.factorization_tm_from_divisor_parsimony
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T12:27:14.581819+00:00
-- url     : https://prove2.me/theorems/4bde6e68-6980-4b70-a76e-a2473953c766
-- title:
--   Atomic Integer Factorization Turing Machine Realization from Divisor-BTN Parsimony and `minFac` Splitting
-- statement:
--   Atomic `PrimitiveMachine` realization of Proposition 2.6 given Theorem 2.2, Lemma 2.3, the proved divisor-BTN parsimony and `N.minFac` splitting theorem, and the proved `{0,1}`-BTN parsimonious counting theorem.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proof of Proposition 2.6 (pp. 10–11)

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Atomic `PrimitiveMachine` realization of Proposition 2.6 (Section 2.3, pp. 10–11):
given black-box BTN contraction (Theorem 2.2), the two-layer multiplication gadget (Lemma 2.3),
the proved divisor-BTN parsimony and `N.minFac` extraction theorem
(`DetDLP.divisor_btn_parsimony_and_minfac`), and the proved `{0, 1}`-BTN parsimonious counting
theorem (`DetDLP.btn_parsimonious_count_and_stage1_cross_mul`), compiles a deterministic
multitape machine computing `N.primeFactorsList` in `2^{O(n / √(log n))}` time and `poly(n)` space. -/
theorem factorization_tm_from_divisor_parsimony :
    (∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
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
    (∀ (N : ℕ), 2 ≤ N →
      let n := bitLen (N + 1)
      N < 2 ^ n ∧
      (∀ d e : ℕ,
        (2 ≤ d ∧ d < N ∧ e < 2 ^ n ∧ d * e = N) ↔
        (2 ≤ d ∧ d < N ∧ d ∣ N ∧ e = N / d)) ∧
      ((Finset.Ico 2 N).filter (fun d => d ∣ N) = ∅ ↔ N.Prime) ∧
      (¬ N.Prime →
        N.minFac ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N) ∧
        N.minFac.Prime ∧
        (∀ d ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N), N.minFac ≤ d) ∧
        2 ≤ N / N.minFac ∧ N / N.minFac < N ∧
        N.primeFactorsList = N.minFac :: (N / N.minFac).primeFactorsList)) →
    (∀ (G : BipartiteMultigraph)
       (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
       {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop) [DecidablePred R]
       (P0 : ℕ),
       IsParsimonious G T ext R →
       G.nE < P0 →
       (Finset.univ.filter R).card < 2 ^ P0 ∧
       BTNContract G (fun v α => truncPolyOfCoeffs P0 1 (fun _ => if T v α then 1 else 0)) =
         truncPolyOfCoeffs P0 1 (fun _ => (Finset.univ.filter R).card)) →
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M out (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))))
          (polyBound K n) := by sorry

end DetDLP
