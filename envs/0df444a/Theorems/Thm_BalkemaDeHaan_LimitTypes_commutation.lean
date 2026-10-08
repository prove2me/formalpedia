-- Prove2me | Theorems.Thm_BalkemaDeHaan_LimitTypes_commutation
-- name    : BalkemaDeHaan.LimitTypes.commutation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:18:58.039903+00:00
-- url     : https://prove2.me/theorems/9f6658c7-9f0c-4833-8428-a7beb2bbcc13
-- title:
--   Proof of Theorem 1, Case 2, display — the affine maps B(y_i) + xA(y_i) commute: B(y₁) + A(y₁)B(y₂) = B(y₂) + A(y₂)B(y₁)
-- statement:
--   Assume the hypotheses of Lemma 1: $R(x) > 0$ for all $x$, $a(t) > 0$, (2) holds with limit $S$, and $1 - S$ is a nondegenerate distribution function. Let $y_1, y_2$ be continuity points of $S$ with $S(y_i) < 1$, and let $(A(y_i), B(y_i))$ with $A(y_i) \ge 1$ satisfy (4) at $y_i$:
--   $$S(x)S(y_i) = S\big(B(y_i) + xA(y_i)\big) \qquad \text{whenever } S(x) < 1, \quad i = 1, 2.$$
--   Then the affine maps $\alpha_i(x) = B(y_i) + xA(y_i)$ commute, that is,
--   $$B(y_1) + A(y_1)B(y_2) = B(y_2) + A(y_2)B(y_1).$$
--
--   In Case 2 of the proof of Theorem 1 this shows that all maps $\alpha_i$ share one fixed point $x_0$, which reduces (4) to a multiplicative form.
--
--   **Formalization Note** Normalization (2). The paper derives the identity inside Case 2, but the derivation uses only (4) and the facts that $S$ is non-increasing and $\log S$ unbounded below; the statement is posed without the Case 2 assumption (in Case 1, $A(y_1) = A(y_2) = 1$, it is the identity $B_1 + B_2 = B_2 + B_1$).
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 796 (PDF 5), proof of Theorem 1, Case 2, display

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- Proof of Theorem 1, Case 2, p. 796 (PDF 5), display: for two continuity points `y₁, y₂` of
`S` with `S(yᵢ) < 1` and pairs `(Aᵢ, Bᵢ)` of Lemma 1 (`Aᵢ ≥ 1`, (4) at `yᵢ`), the affine maps
`αᵢ(x) = Bᵢ + x Aᵢ` commute: `B₁ + A₁ B₂ = B₂ + A₂ B₁`. -/
theorem commutation
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hR : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (a b : ℝ → ℝ) (ha : ∀ t : ℝ, 0 < a t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c)
    (h2 : WeakConv (normedTail μ a b) (tail ν))
    (y₁ y₂ : ℝ) (hy₁c : ContinuousAt (tail ν) y₁) (hy₁ : tail ν y₁ < 1)
    (hy₂c : ContinuousAt (tail ν) y₂) (hy₂ : tail ν y₂ < 1)
    (A₁ B₁ A₂ B₂ : ℝ) (hA₁ : 1 ≤ A₁) (hA₂ : 1 ≤ A₂)
    (h4₁ : ∀ x : ℝ, tail ν x < 1 → tail ν x * tail ν y₁ = tail ν (B₁ + x * A₁))
    (h4₂ : ∀ x : ℝ, tail ν x < 1 → tail ν x * tail ν y₂ = tail ν (B₂ + x * A₂)) :
    B₁ + A₁ * B₂ = B₂ + A₂ * B₁ := by sorry

end BalkemaDeHaan.LimitTypes
