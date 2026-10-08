-- Prove2me | Theorems.Thm_ConvexOptAlg_StrongGD_phi_convex_smooth
-- name    : ConvexOptAlg.StrongGD.phi_convex_smooth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:21:17.409159+00:00
-- url     : https://prove2.me/theorems/4d00018b-190f-47e0-89f4-adc2d388f1c3
-- title:
--   Proof of Lemma 3.11, p. 279 — φ is convex and (β − α)-smooth
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\alpha$-strongly convex and $\beta$-smooth with gradient $g$, where $n\ge1$ and $\alpha>0$. Define $\phi(z)=f(z)-(\alpha/2)\|z\|^2$. Then $\phi$ is convex, its gradient is $g(z)-\alpha z$, and
--   $$\|(g(x)-\alpha x)-(g(y)-\alpha y)\|\le(\beta-\alpha)\|x-y\|\qquad(x,y\in\mathbb R^n).$$
--
--   This shifted function supplies the convex smooth object to which Equation (3.6) applies in the proof of Lemma 3.11.
--
--   **Formalization Note** Positive dimension excludes the zero-dimensional space, where strong convexity imposes no restriction on $\beta-\alpha$.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Lemma 3.11, p. 279

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace

namespace ConvexOptAlg.StrongGD

/-- The auxiliary function in the proof of Lemma 3.11, p. 279. -/
theorem phi_convex_smooth {n : ℕ} (hn : 0 < n) (f : E n → ℝ)
    (g : E n → E n) (α β : ℝ) (hα : 0 < α)
    (hsm : IsBetaSmooth f g β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α) :
    ConvexOn ℝ (Set.univ : Set (E n)) (phi f α) ∧
      IsBetaSmooth (phi f α) (fun z => g z - α • z) (β - α) := by sorry

end ConvexOptAlg.StrongGD
