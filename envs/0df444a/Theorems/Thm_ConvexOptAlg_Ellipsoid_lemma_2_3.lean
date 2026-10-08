-- Prove2me | Theorems.Thm_ConvexOptAlg_Ellipsoid_lemma_2_3
-- name    : ConvexOptAlg.Ellipsoid.lemma_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:30:54.929993+00:00
-- url     : https://prove2.me/theorems/f2f55795-5674-4b18-96f3-422b2a3c18fe
-- title:
--   Lemma 2.3, p. 247 — a half-ellipsoid fits in an ellipsoid of volume ≤ exp(−1/(2n))·vol(E₀), explicitly (2.5)–(2.6) for n ≥ 2
-- statement:
--   Let $\mathcal E_0=\{x\in\mathbb R^n:(x-c_0)^\top H_0^{-1}(x-c_0)\le 1\}$ with $c_0\in\mathbb R^n$ and $H_0$ symmetric positive definite, and let $w\in\mathbb R^n$, $w\ne0$. Then:
--
--   1. there exists an ellipsoid $\mathcal E=\{x:(x-c)^\top H^{-1}(x-c)\le 1\}$, $H$ symmetric positive definite, with
--   $$
--   \mathcal E\supset\{x\in\mathcal E_0: w^\top(x-c_0)\le0\}\quad(2.3)\qquad\text{and}\qquad \mathrm{vol}(\mathcal E)\le\exp\Big(-\frac1{2n}\Big)\mathrm{vol}(\mathcal E_0)\quad(2.4);
--   $$
--   2. for $n\ge2$ one can take
--   $$
--   c=c_0-\frac1{n+1}\frac{H_0w}{\sqrt{w^\top H_0w}}\quad(2.5),\qquad H=\frac{n^2}{n^2-1}\Big(H_0-\frac2{n+1}\frac{H_0ww^\top H_0}{w^\top H_0w}\Big)\quad(2.6):
--   $$
--   this $H$ is symmetric positive definite and $\mathcal E$ satisfies (2.3) and (2.4).
--
--   This is the geometric step of the ellipsoid method: one cut through the center of the current ellipsoid shrinks the volume of the localizing ellipsoid by the factor $\exp(-1/(2n))$.
--
--   **Formalization Note** $\mathrm{vol}$ is Lebesgue measure on `Fin n → ℝ`, with values in $[0,\infty]$; ellipsoids are the published `LinearOptimization.ellipsoid`. "Ellipsoid" in part 1 means a positive definite shape matrix. The published, proved `LinearOptimization.ellipsoid_update_halfspace_volume` gives (2.3) and positive definiteness for (2.5)–(2.6) with $a=-w$, but only the weaker volume factor $\exp(-1/(2(n+1)))$; the book's factor $\exp(-1/(2n))$ is kept here.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 2.3, eqs. (2.3)–(2.6), p. 247

import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

namespace ConvexOptAlg.Ellipsoid

open Matrix MeasureTheory

/-- **Lemma 2.3** (Bubeck, arXiv:1405.4980v2, p. 247). Let `E₀ = {x : (x − c₀)⊤H₀⁻¹(x − c₀) ≤ 1}`
with `H₀` symmetric positive definite, and let `w ≠ 0`.
(i) There is an ellipsoid `E` (center `c`, symmetric positive definite matrix `H`) containing
the half-ellipsoid `{x ∈ E₀ : w⊤(x − c₀) ≤ 0}` (2.3) with `vol(E) ≤ exp(−1/(2n)) vol(E₀)` (2.4).
(ii) For `n ≥ 2` one can take `c = c₀ − (1/(n+1)) H₀w/√(w⊤H₀w)` (2.5) and
`H = (n²/(n²−1)) (H₀ − (2/(n+1)) H₀ww⊤H₀/(w⊤H₀w))` (2.6): this `H` is positive definite and
`E` satisfies (2.3) and (2.4). Volume is Lebesgue measure on `ℝⁿ = Fin n → ℝ`. -/
theorem lemma_2_3 {n : ℕ} (c0 : Fin n → ℝ) (H0 : Matrix (Fin n) (Fin n) ℝ) (hH0 : H0.PosDef)
    (w : Fin n → ℝ) (hw : w ≠ 0) :
    (∃ (c : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.PosDef ∧
      LinearOptimization.ellipsoid c0 H0 ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
        LinearOptimization.ellipsoid c H ∧
      volume (LinearOptimization.ellipsoid c H) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * (n : ℝ)))) *
          volume (LinearOptimization.ellipsoid c0 H0)) ∧
    (2 ≤ n →
      (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
          (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
            (H0 * vecMulVec w w * H0))).PosDef ∧
      LinearOptimization.ellipsoid c0 H0 ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
        LinearOptimization.ellipsoid
          (c0 - ((1 : ℝ) / ((n : ℝ) + 1)) • (Real.sqrt (w ⬝ᵥ (H0 *ᵥ w)))⁻¹ • (H0 *ᵥ w))
          (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
            (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
              (H0 * vecMulVec w w * H0))) ∧
      volume (LinearOptimization.ellipsoid
          (c0 - ((1 : ℝ) / ((n : ℝ) + 1)) • (Real.sqrt (w ⬝ᵥ (H0 *ᵥ w)))⁻¹ • (H0 *ᵥ w))
          (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
            (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
              (H0 * vecMulVec w w * H0)))) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * (n : ℝ)))) *
          volume (LinearOptimization.ellipsoid c0 H0)) := by sorry

end ConvexOptAlg.Ellipsoid
