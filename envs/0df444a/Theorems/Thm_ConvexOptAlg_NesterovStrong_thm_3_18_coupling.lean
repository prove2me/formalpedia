-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovStrong_thm_3_18_coupling
-- name    : ConvexOptAlg.NesterovStrong.thm_3_18_coupling
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:01:12.743165+00:00
-- url     : https://prove2.me/theorems/a22fdaf9-f2b6-4502-9528-f36145c693ba
-- title:
--   Proof of Theorem 3.18, p. 293 — v_s − x_s = √κ(x_s − y_s)
-- statement:
--   Let $\alpha,\beta>0$, $\kappa=\beta/\alpha$, let $g:\mathbb R^n\to\mathbb R^n$ be any map (in the role of $\nabla f$), let $(x_t),(y_t)$ be a run of Nesterov's accelerated gradient descent with this map, and let $v_s$ be defined from the points $x_s$ by (3.21) with $v_1=x_1$. Then for every $s\ge1$,
--   $$v_s-x_s=\sqrt\kappa\,(x_s-y_s).$$
--
--   This ties the centre $v_s$ of the model $\Phi_s$ to the two sequences of the method; it is the identity that turns (3.22) into (3.20), and it explains the momentum coefficient $(\sqrt\kappa-1)/(\sqrt\kappa+1)$.
--
--   **Formalization Note** The identity is algebraic: it uses only the recursions of the method and of $v_s$, so no convexity or smoothness of a function is assumed.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.18, p. 293, "Finally we show by induction that v_s − x_s = √κ(x_s − y_s)"

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovStrong

/-- Bubeck, proof of Theorem 3.18, p. 293 ("Finally we show by induction that …"): for
`α, β > 0`, any gradient map `g` and a run `(x, y)` of Nesterov's accelerated gradient descent,
the centres `v_s` of (3.21) satisfy `v_s − x_s = √κ (x_s − y_s)` for every `s ≥ 1`. -/
theorem thm_3_18_coupling {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (s : ℕ) (hs : 1 ≤ s) :
    v g α β x s - x s = Real.sqrt (kappa α β) • (x s - y s) := by sorry

end ConvexOptAlg.NesterovStrong
