-- Prove2me | Theorems.Thm_DetDLP_theorem_4_3_tm_from_lemma_5_2
-- name    : DetDLP.theorem_4_3_tm_from_lemma_5_2
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T11:23:34.173988+00:00
-- url     : https://prove2.me/theorems/6c9f5dd7-cb2d-4b0d-9451-1ce69bb2040a
-- title:
--   Terminal-Preserving Contraction Machine via Partial Core Expansion and Digit Reduction
-- statement:
--   Assuming degree-sensitive scalar contraction (`DetDLP.lemma_5_2_degree_sensitive_contraction`) and the 2-adic guard-bit, Kronecker-packing, and $L_1$-norm identities (`DetDLP.section5_guard_and_kronecker`), every lookup-separator bipartite BTN $\mathcal{N}_y$ with $4m$ lookup vertices of total arity $\beta = 4mk = \Theta(b)$ contracts deterministically in $(S + \mathcal{L})^{O(1)} 2^{O(b/\sqrt{\log\log b})}$ bit operations and $(S + \mathcal{L})^{O(1)}$ bits of space.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 5.3, Lemma 5.3 & Proof of Theorem 4.3 (pp. 20–22)

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_DetDLP_TerminalBTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- Partial core expansion + digit-reduction + Kronecker-packed `Lemma 5.2` contraction +
guard-bit recovery realizing Theorem 4.3 (Section 5.3, pp. 20–22):
assuming degree-sensitive contraction (`lemma_5_2_degree_sensitive_contraction`) and the
exact guard-bit / Kronecker / `L_1`-norm identities (`section5_guard_and_kronecker`), every
lookup-separator BTN satisfies Theorem 4.3. -/
theorem theorem_4_3_tm_from_lemma_5_2 :
    (∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ'),
            2 ≤ β → 1 ≤ Told → G.nE ≤ C * β → G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β → 1 ≤ ℓ' → ℓ' ≤ C * β →
            BTNEntryEvaluable desc G P ℓ' T E outE (Told : ℝ) (((β + desc.length : ℕ) : ℝ) ^ c0) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            ∃ w : List Bool,
              EncodesTruncPoly P ℓ' w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
                (polyBound K (β + desc.length) * (Told : ℝ) *
                  (2 : ℝ) ^ ((K : ℝ) * (β : ℝ) / Real.sqrt (ρ : ℝ)))
                (polyBound K (β + desc.length))) →
    ((∀ P0 Qguard r acc : ℕ,
        r < 2 ^ P0 →
        acc < 2 ^ (P0 + Qguard) →
        (acc : ℤ) ≡ ((2 ^ Qguard * r : ℕ) : ℤ) [ZMOD ((2 ^ (P0 + Qguard) : ℕ) : ℤ)] →
        acc = 2 ^ Qguard * r ∧ acc / 2 ^ Qguard = r) ∧
      (∀ K0 ℓ : ℕ, 1 ≤ K0 → 1 ≤ ℓ →
        (∀ i1 i1' i2 i2' : ℕ, i1 < K0 → i1' < K0 →
          i1 + K0 * i2 = i1' + K0 * i2' → i1 = i1' ∧ i2 = i2') ∧
        (∀ i1 i2 : ℕ, i1 < K0 → i2 < ℓ → i1 + K0 * i2 < K0 * ℓ) ∧
        (∀ i1 i2 : ℕ, ℓ ≤ i2 → K0 * ℓ ≤ i1 + K0 * i2)) ∧
      (∀ (n B : ℕ) (p : Fin n → Polynomial ℕ),
        (∀ j : Fin n, (p j).eval 1 ≤ B) →
        (∏ j : Fin n, p j).eval 1 ≤ B ^ n ∧
        ∀ d : ℕ, (∏ j : Fin n, p j).coeff d ≤ B ^ n)) →
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (b m k S P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ b → 1 ≤ m → 1 ≤ k →
            blockCount b ≤ C * m → m ≤ C * blockCount b →
            S ≤ C * m * b →
            4 * m * k ≤ C * b → b ≤ C * (4 * m * k) →
            1 ≤ P0 → P0 ≤ S → 1 ≤ ℓ → ℓ ≤ C * m →
            G.nV ≤ (S + desc.length + 1) ^ c0 →
            ∀ (spec : LookupSeparatorSpec G m k S (C * Nat.ceil ((b : ℝ) ^ ((3 : ℝ) / 4)))),
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (polyBound c0 (S + desc.length)) (polyBound c0 (S + desc.length)) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeTerminalBTNInstance desc G b m k S P0 ℓ spec.lookupVerts) w
                (polyBound K (S + desc.length) * mainTimeBound K b)
                (polyBound K (S + desc.length)) := by
  sorry

end DetDLP
