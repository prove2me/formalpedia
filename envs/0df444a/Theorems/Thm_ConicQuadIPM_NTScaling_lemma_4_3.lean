-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_lemma_4_3
-- name    : ConicQuadIPM.NTScaling.lemma_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:26.903953+00:00
-- url     : https://prove2.me/theorems/25038599-ab5c-4d39-aba3-9b7c6a334f35
-- title:
--   Lemma 4.3, p. 16 — (θW)⁻² = θ⁻² Q W² Q for a scaling matrix W
-- statement:
--   Let $K$ be one of $\mathbb R_+$, $K^q$, $K^r$ with matrix $Q$, let $\theta>0$ and let $W$ be a scaling matrix ($W\succ0$, $WQW=Q$). Then
--   $$(\theta W)^{-2} = \theta^{-2}\,Q\,W^2\,Q.$$
--
--   So the inverse square of the scaling, needed in the scaled Newton system (27), costs no more than $W^2$ itself.
--
--   **Formalization Note** The statement is made for one cone block $K^i$, with the superscript $i$ dropped: $\Theta$ and $W$ are block diagonal (p. 11–12), so the per-block statement is the paper's statement block by block. Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The dimension conventions the paper leaves implicit ($d=1$ for $\mathbb R_+$, $d\ge 1$ for $K^q$, $d\ge2$ for $K^r$) are the hypothesis `WellFormedBlock kind d`. The paper states the lemma for "$W^i$ given as in Lemma 4.2"; its proof uses only Definition 3.3 and $QQ=I$, so it is stated here for every scaling matrix (a generalization, which contains the paper's case). $(\theta W)^{-2}$ is written $(\theta W)^{-1}(\theta W)^{-1}$.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 16, Lemma 4.3 and its proof

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- Lemma 4.3, p. 16, for one cone block and every scaling matrix `W`:
`(θW)⁻² = θ⁻² Q W² Q`. -/
theorem lemma_4_3 (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (θ : ℝ) (hθ : 0 < θ) (W : Matrix (Fin d) (Fin d) ℝ) (hW : IsScaling kind d W) :
    (θ • W)⁻¹ * (θ • W)⁻¹ = (θ ^ 2)⁻¹ • (Qmat kind d * (W * W) * Qmat kind d) := by sorry
end ConicQuadIPM.NTScaling
