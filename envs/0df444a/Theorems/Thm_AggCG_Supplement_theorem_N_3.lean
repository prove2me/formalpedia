-- Prove2me | Theorems.Thm_AggCG_Supplement_theorem_N_3
-- name    : AggCG.Supplement.theorem_N_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:37:39.333876+00:00
-- url     : https://prove2.me/theorems/b9f9f039-135f-496f-9186-32b773d8724a
-- title:
--   Theorem N.3 — scalar ridge capacity
-- statement:
--   For every $p\ge2$, the scalar ridge validation-loss class over all full-column-rank $p$-coefficient tasks has pseudo-dimension $\Theta(\log p)$. Moreover, there are $d=\lfloor\log_2p\rfloor$ rational tasks, each with $p$ training samples and one validation point, that are $1/2$-fat-shattered by $2^d$ parameter witnesses in $[1,2]$.
--
--   The constructed Gram matrices have eigenvalues between universal positive constants, and all training and validation data have polynomial bit length. Large validation-feature norms are allowed.
--
--   Differences from the source:
--   - encoding: universal Gram eigenvalue bounds, polynomial bit length, and $\Theta(\log p)$ pseudo-dimension → uniform quadratic-form constants, a uniform polynomial bound on rational codes, and one exact pseudo-dimension $D$ between universal multiples of $\log p$; reason: these are equivalent finite-dimensional and asymptotic formulations of the three source clauses
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem N.3, p.78, PDF p.79

import Mathlib
import Definitions.Def_FoundationsML_Regression_PseudoDim
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_AggCG_Supplement_ridgeClass

namespace AggCG.Supplement

open Matrix

/-- **Theorem N.3** (Scalar ridge capacity; Sharma, *Computational Complexity of Data-Driven Configuration
for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission (manuscript sha256
f7ea0248…), p.78, PDF p.79). With universal constants and one polynomial bit bound, for every integer
`p ≥ 2`:
(1) the scalar regularization-parameter family `F` of nonnegative squared validation losses on all
full-column-rank ridge tasks with `p` coefficients has `Pdim(F) = Θ(log p)`;
(2) there are `d = ⌊log₂ p⌋` rational full-rank ridge-training/one-point-validation tasks, each with `p`
coefficients and `p` training samples, which `F` `1/2`-fat-shatters using `2^d` parameter witnesses in
`[1, 2]` (so `fat_{1/2}(F) ≥ d`); their training Gram matrices have eigenvalues between two universal
positive constants, and all training and validation data have rational encodings of polynomial bit length.

**Formalization Note** The Gram bound `c₁ ≤ eig(XᵀX) ≤ c₂` is stated as `c₁‖v‖² ≤ ‖Xv‖² ≤ c₂‖v‖²`. The
fat-shattering clause is for the subfamily `λ ∈ [1, 2]` on the `d` tasks, which places the witnesses in
`[1, 2]` and implies the clause for `F`. -/
theorem theorem_N_3 :
    ∃ (c₁ c₂ cl Cu : ℝ) (cb e : ℕ), 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < cl ∧ 0 < Cu ∧ ∀ p : ℕ, 2 ≤ p →
      (∃ D : ℕ, FoundationsML.Regression.PseudoDim (ridgeClass p) D ∧
        cl * Real.log p ≤ D ∧ (D : ℝ) ≤ Cu * Real.log p) ∧
      ∃ (X : Fin (Nat.log 2 p) → Matrix (Fin p) (Fin p) ℚ) (y : Fin (Nat.log 2 p) → Fin p → ℚ)
        (r : Fin (Nat.log 2 p) → Fin p → ℚ) (t : Fin (Nat.log 2 p) → ℚ),
        let task : Fin (Nat.log 2 p) → RidgeTask p := fun i =>
          ⟨p, (X i).map ((↑) : ℚ → ℝ), fun k => (y i k : ℝ), fun k => (r i k : ℝ), (t i : ℝ)⟩
        (∀ i, (task i).FullRank) ∧
        (∀ i (v : Fin p → ℝ), c₁ * ∑ k, v k ^ 2 ≤ ∑ k, ((task i).X *ᵥ v) k ^ 2 ∧
          ∑ k, ((task i).X *ᵥ v) k ^ 2 ≤ c₂ * ∑ k, v k ^ 2) ∧
        (∀ i a b, (QAlgorithms.LocalHamiltonian.encRat (X i a b)).length ≤ cb * (p + 1) ^ e ∧
          (QAlgorithms.LocalHamiltonian.encRat (y i a)).length ≤ cb * (p + 1) ^ e ∧
          (QAlgorithms.LocalHamiltonian.encRat (r i a)).length ≤ cb * (p + 1) ^ e ∧
          (QAlgorithms.LocalHamiltonian.encRat (t i)).length ≤ cb * (p + 1) ^ e) ∧
        BartlettNN.Margin.GammaShatters
          {g : Fin (Nat.log 2 p) → ℝ | ∃ lam ∈ Set.Icc (1 : ℝ) 2, ∀ i, g i = (task i).loss lam} (1 / 2) id := by sorry

end AggCG.Supplement
