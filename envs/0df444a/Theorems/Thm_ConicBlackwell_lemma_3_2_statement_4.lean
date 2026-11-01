-- Prove2me | Theorems.Thm_ConicBlackwell_lemma_3_2_statement_4
-- name    : ConicBlackwell.lemma_3_2_statement_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:42:29.315992+00:00
-- url     : https://prove2.me/theorems/25e47273-eeab-48ea-8e23-58f12fd456ee
-- title:
--   Lemma 3.2, Statement 4 — $\mathcal C^\circ$ is a closed convex cone and $-\mathcal C\subseteq\mathcal C^\circ$ for $\mathcal C=\operatorname{cone}(\{\kappa\}\times\mathcal X)$
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a nonempty convex compact set, $\kappa=\max_{x\in\mathcal X}\|x\|_2$, and $\mathcal C=\operatorname{cone}(\{\kappa\}\times\mathcal X)=\{\alpha(\kappa,x):\alpha\ge0,\ x\in\mathcal X\}\subset\mathbb R^{n+1}$. Then
--
--   1. the polar $\mathcal C^\circ$ is a closed convex cone, and
--   2. if $u\in\mathcal C$, then $-u\in\mathcal C^\circ$.
--
--   The second part is what makes the correction terms $-\sum_t(\theta_{t+1}/\omega_{t+1}-\theta_t/\omega_t)u_t$ in the proof of Theorem 3.3 harmless for the order $\le_{\mathcal C^\circ}$.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: κ = max_{x∈X} ‖x‖₂ and v_t = (⟨f_t, x_t⟩/κ, −f_t) → kappa X = sSup of ‖x‖ over X, and payoff X x f = lift (⟪f, x⟫ / kappa X) (−f) with Lean's x/0 = 0; reason: sSup is the max on a nonempty compact X; κ = 0 only when X = {0}, where the page's ⟨f,x⟩/κ is undefined and both coordinates conventions give the same statement
--   - encoding: the lemma's standing hypothesis 'C is a closed convex cone' → not stated as a hypothesis; reason: cone({κ} × X) is a closed convex cone for every nonempty convex compact X (κ > 0 gives 0 ∉ {κ} × X; κ = 0 gives X = {0} and C = {0}), so the hypothesis excludes nothing
--   - encoding: C° is a closed convex cone → MoreauProx.Decomposition.IsClosedConvexCone (target X), target X = polar (cone (lift (kappa X) '' X)); reason: the published definitions of the cone and its polar; a polar always contains 0, so the nonemptiness clause adds nothing
--   - reading: X ⊂ ℝⁿ convex compact → X nonempty, convex, compact; reason: the paper's X contains the decisions x₀, x₁ (Algorithm 1, p.5–6)
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Lemma 3.2, Statement 4, p.7

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **Lemma 3.2, Statement 4**, Grand-Clément & Kroer, arXiv:2202.12277v1, p.7.
Assume that `C = cone({κ} × X)` with `X ⊂ ℝⁿ` convex compact and `κ = max_{x∈X} ‖x‖₂`.  Then
`C°` is a closed convex cone.  Additionally, if `u ∈ C` we have `−u ∈ C°`.

Formalization Note: `C = cone (lift (kappa X) '' X)` and `C° = target X = polar C`
(`ApproachRegret.ToOLO`).  Nonemptiness of `X` (implicit in the paper, where `x₁ ∈ X`) is kept. -/
theorem lemma_3_2_statement_4 {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X) :
    MoreauProx.Decomposition.IsClosedConvexCone (target X) ∧
      ∀ u ∈ cone (lift (kappa X) '' X), -u ∈ target X := by sorry

end ConicBlackwell
