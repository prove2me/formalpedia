-- Prove2me | Theorems.Thm_AubinLipschitz_robinson_ursescu
-- name    : AubinLipschitz.robinson_ursescu
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:20.66892+00:00
-- url     : https://prove2.me/theorems/2ab649e5-3fd3-4c15-bdf0-39521b689ade
-- title:
--   §3, (17) — the Robinson–Ursescu theorem
-- statement:
--   Let $G$ be a surjective closed convex process between finite-dimensional normed spaces $X$ and $Y$. Then there is $\gamma>0$ with
--
--   $$
--   \gamma B\subset G(B),
--   $$
--
--   that is, every $v\in Y$ with $\|v\|\le\gamma$ lies in $G(u)$ for some $u$ with $\|u\|\le1$.
--
--   This is the open mapping principle for closed convex processes.
--
--   Differences from the source:
--   - generalization: applied at (17) to the process G = CF(x₀,y₀) → any surjective closed convex process; reason: this is the form of the cited theorem, and the Clarke derivative is such a process by §2, p.16.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, proof of Lemma 1, display (17), p.27

import Mathlib
import Definitions.Def_AubinLipschitz_IsClosedConvexProcess
import Definitions.Def_AubinLipschitz_IsSurjectiveProcess

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, proof of Lemma 1, display (17), p.27 (Robinson–Ursescu): a surjective closed
convex process `G` between finite-dimensional spaces satisfies `γB ⊂ G(B)` for some `γ > 0`. -/
theorem robinson_ursescu {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (G : X → Set Y) (hG : IsClosedConvexProcess G) (hsurj : IsSurjectiveProcess G) :
    ∃ γ > 0, ∀ v : Y, ‖v‖ ≤ γ → ∃ u : X, ‖u‖ ≤ 1 ∧ v ∈ G u := by sorry

end AubinLipschitz
