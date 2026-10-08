-- Prove2me | Theorems.Thm_ChenStein_OneVar_theorem_1
-- name    : ChenStein.OneVar.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:31:55.026968+00:00
-- url     : https://prove2.me/theorems/c3d05764-8c11-4f4e-92d5-d0b8c192294f
-- title:
--   Theorem 1, p. 11 — total variation and zero-count bounds
-- statement:
--   Let $W$ count a family of dependent Bernoulli events and let $Z$ be Poisson with their common mean $\lambda>0$. Using the paper's total variation norm, which is twice the supremum over events,
--
--   $$
--   \begin{aligned}
--   \|\mathcal L(W)-\mathcal L(Z)\|&\le2\left[(b_1+b_2)\frac{1-e^{-\lambda}}{\lambda}+b'_3\min\{1,1.4\lambda^{-1/2}\}\right]\le2(b_1+b_2+b_3),\\
--   |P(W=0)-e^{-\lambda}|&\le(b_1+b_2+b'_3)\frac{1-e^{-\lambda}}{\lambda}<\min\{1,\lambda^{-1}\}(b_1+b_2+b_3).
--   \end{aligned}
--   $$
--
--   This controls both the complete count distribution and the probability that no event occurs, with the paper's exact coefficients.
--
--   **Formalization Note** The index set is countable; the indicators are measurable and take values in $\{0,1\}$; all $p_\alpha$ are positive with `HasSum` equal to $\lambda$; and every neighbourhood contains its own index. The four clauses use extended nonnegative error sums. Only the strict final comparison is conditional on $b_1+b_2+b_3<\infty$, since strict $\infty<\infty$ is false.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), p. 11, Theorem 1; https://doi.org/10.1214/aop/1176991491

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_ChenStein_OneVar_Setting

namespace ChenStein.OneVar

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Arratia--Goldstein--Gordon (1989), p. 11, Theorem 1. -/
theorem theorem_1 {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α))
    (hX01 : ∀ α ω, X α ω ≤ 1)
    (hp : ∀ α, 0 < p P X α)
    (lam : ℝ) (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α) :
    let q := (1 - Real.exp (-lam)) / lam
    let a := b1 P X B + b2 P X B
    let c := b3 P X B
    let c' := b3' P X B
    let firstBound := 2 * (a * ENNReal.ofReal q +
      c' * ENNReal.ofReal (min 1 (1.4 * lam ^ (-(1/2 : ℝ)))))
    ENNReal.ofReal (2 * MarkovChainCLT.tvDist (P.map (W X))
      (poissonMeasure lam.toNNReal)) ≤ firstBound ∧
    firstBound ≤ 2 * (a + c) ∧
    ENNReal.ofReal |P.real {ω | W X ω = 0} - Real.exp (-lam)| ≤
      (a + c') * ENNReal.ofReal q ∧
    (a + c < ⊤ →
      (a + c') * ENNReal.ofReal q <
        ENNReal.ofReal (min 1 lam⁻¹) * (a + c)) := by sorry

end ChenStein.OneVar
