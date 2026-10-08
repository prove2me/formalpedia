-- Prove2me | Theorems.Thm_ConvexOptAlg_StrongGD_one_step_contraction
-- name    : ConvexOptAlg.StrongGD.one_step_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:21:52.659982+00:00
-- url     : https://prove2.me/theorems/514990b8-22a8-4918-9ad4-3559fadeede3
-- title:
--   Proof of Theorem 3.12, p. 279 — one-step squared-distance contraction
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\alpha$-strongly convex and $\beta$-smooth with gradient $g$, where $n\ge1$ and $\alpha>0$. Let $x^*$ minimize $f$ and let gradient descent run with $\eta=2/(\alpha+\beta)$. Writing $\kappa=\beta/\alpha$, for each $t\ge1$,
--   $$\|x_{t+1}-x^*\|^2\le\left(\frac{\kappa-1}{\kappa+1}\right)^2\|x_t-x^*\|^2.$$
--
--   This is the per-iteration contraction obtained from Lemma 3.11.
--
--   **Formalization Note** The printed proof immediately compares this one-step term to a bound involving $x_1$; that final comparison belongs to the iterated bound below.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.12, p. 279, contraction display

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace

namespace ConvexOptAlg.StrongGD

/-- The one-step inequality in the proof of Theorem 3.12, p. 279. -/
theorem one_step_contraction {n : ℕ} (hn : 0 < n) (f : E n → ℝ)
    (g : E n → E n) (α β : ℝ) (hα : 0 < α)
    (hsm : IsBetaSmooth f g β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (xstar : E n) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → E n) (hrun : IsGDRun g (2 / (α + β)) x) :
    ∀ t : ℕ, 1 ≤ t →
      ‖x (t + 1) - xstar‖ ^ 2 ≤
        ((β / α - 1) / (β / α + 1)) ^ 2 * ‖x t - xstar‖ ^ 2 := by sorry

end ConvexOptAlg.StrongGD
