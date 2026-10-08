-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_lemma_3_3_i_iii
-- name    : ConicQuadIPM.NTScaling.lemma_3_3_i_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:53.059898+00:00
-- url     : https://prove2.me/theorems/1538922c-e3d1-4f2f-9790-21ecd4c60012
-- title:
--   Lemma 3.3 i)–iii), p. 12 — scaling preserves xᵀs and rescales xᵀQx by θ², sᵀQs by θ⁻²
-- statement:
--   Let $K$ be one of $\mathbb R_+$, $K^q$, $K^r$ in dimension $d$, with matrix $Q$ of Definition 3.2. Let $\theta>0$, let $W$ be a scaling matrix ($W\succ 0$, $WQW = Q$), and for $x,s\in\mathbb R^d$ put $\bar x = \theta W x$, $\bar s = (\theta W)^{-1}s$. Then
--   $$x^Ts = \bar x^T\bar s,\qquad \theta^2\,x^TQx = \bar x^TQ\bar x,\qquad \theta^{-2}\,s^TQs = \bar s^TQ\bar s.$$
--
--   Scaling therefore leaves the duality gap unchanged and changes the "Lorentz norms" $x^TQx$, $s^TQs$ only by the factors $\theta^{\pm2}$. This is what determines $\theta$ in the Nesterov–Todd scaling (30).
--
--   **Formalization Note** The statement is made for one cone block $K^i$, with the superscript $i$ dropped: $\Theta$ and $W$ are block diagonal (p. 11–12), so the per-block statement is the paper's statement block by block. Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The dimension conventions the paper leaves implicit ($d=1$ for $\mathbb R_+$, $d\ge 1$ for $K^q$, $d\ge2$ for $K^r$) are the hypothesis `WellFormedBlock kind d`. The hypothesis $\theta>0$ is implicit in the paper ($\Theta$ is positive definite, p. 24).
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 12, Lemma 3.3 i)–iii); proof p. 37

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- Lemma 3.3 i)–iii), p. 12, for one cone block. -/
theorem lemma_3_3_i_iii (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (θ : ℝ) (hθ : 0 < θ) (W : Matrix (Fin d) (Fin d) ℝ) (hW : IsScaling kind d W)
    (x s : Fin d → ℝ) :
    x ⬝ᵥ s = xbar θ W x ⬝ᵥ sbar θ W s ∧
    θ ^ 2 * (x ⬝ᵥ (Qmat kind d *ᵥ x)) = xbar θ W x ⬝ᵥ (Qmat kind d *ᵥ xbar θ W x) ∧
    (θ ^ 2)⁻¹ * (s ⬝ᵥ (Qmat kind d *ᵥ s)) = sbar θ W s ⬝ᵥ (Qmat kind d *ᵥ sbar θ W s) := by sorry
end ConicQuadIPM.NTScaling
