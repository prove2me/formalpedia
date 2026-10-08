-- Prove2me | Theorems.Thm_ConvexOptAlg_SVRG_unbiased_direction
-- name    : ConvexOptAlg.SVRG.unbiased_direction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:45:16.934408+00:00
-- url     : https://prove2.me/theorems/85c6c166-3c5e-439a-8a08-6d80c7b79448
-- title:
--   §6.3, p. 337 — unbiased SVRG direction
-- statement:
--   Under the component assumptions of §6.3, let $x^*$ minimize $f$ and fix $x,y$. With $v_I(x,y)=g_I(x)-g_I(y)+G(y)$ and $I$ uniform in $[m]$,
--
--   $$\mathbb E_I\langle v_I(x,y),x-x^*\rangle=\langle G(x),x-x^*\rangle\ge f(x)-f(x^*).$$
--
--   The first equality identifies the sampled direction's mean with the full gradient; the second inequality is convexity of the average objective. Together they control the drift of an SVRG step.
--
--   **Formalization Note** The expectation averages a single component index at fixed $x,y$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.3, p. 337, PDF p. 110, unnumbered display after Eq. (6.3)

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- The unnumbered display after (6.3), p. 337: the SVRG direction is
unbiased, and convexity bounds its pairing with the displacement from `xstar`. -/
theorem unbiased_direction {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (β : ℝ) (x y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun i : Fin m => ⟪direction gs x y i, x - xstar⟫_ℝ) =
      ⟪fullGradient gs x, x - xstar⟫_ℝ ∧
    objective fs x - objective fs xstar ≤
      ⟪fullGradient gs x, x - xstar⟫_ℝ := by sorry

end ConvexOptAlg.SVRG
