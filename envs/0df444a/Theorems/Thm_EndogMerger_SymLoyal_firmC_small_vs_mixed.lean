-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_firmC_small_vs_mixed
-- name    : EndogMerger.SymLoyal.firmC_small_vs_mixed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:59.226349+00:00
-- url     : https://prove2.me/theorems/c56e2510-6f3a-4c4b-9a5c-50a16b68a773
-- title:
--   Proof of Proposition 3, PDF p. 49 — Π^(BC)_C = Π^(AB)_C for k < k^(AB)_1, and Π^(BC)_C < Π^(AB)_C for k > k^(AB)_1
-- statement:
--   Let $0<\alpha<1/3$, $\alpha<k<1-2\alpha$ and $r>0$. Firm $C$'s Table A1 profit in the small merger, $\Pi^{(BC)}_C=\Pi^{(BC)}/2$, and in the mixed merger, $\Pi^{(AB)}_C$, satisfy
--
--   1. if $k<k^{(AB)}_1(\alpha)$, then $\Pi^{(BC)}_C=\Pi^{(AB)}_C$;
--   2. if $k>k^{(AB)}_1(\alpha)$, then
--   $$
--   \Pi^{(BC)}_C<\Pi^{(AB)}_C .
--   $$
--
--   Together with equality at $k=k^{(AB)}_1$ itself, this gives $\Pi^{(AB)}_C\ge\Pi^{(BC)}_C$ throughout the limited-capacity range, so the second disjunct of (1b) always holds there.
--
--   **Formalization Note** The paper states part 2 on the complement of $\Omega^{(AB)}_2$, which includes $k=k^{(AB)}_1$, where the profits are equal; part 2 is therefore stated for $k>k^{(AB)}_1$. The page treats $(1-\alpha)/2<k<1-2\alpha$ separately; at $k=(1-\alpha)/2$ itself the strict inequality also holds, since $k^{(AB)}_1<(1-\alpha)/2$.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, Appendix H, proof of Proposition 3, PDF p. 49

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting
import Definitions.Def_EndogMerger_SymLoyal_Regions

namespace EndogMerger.SymLoyal
theorem firmC_small_vs_mixed (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (k < kAB₁ α → piBCB α k r = piABC α k r) ∧
    (kAB₁ α < k → piBCB α k r < piABC α k r) := by sorry
end EndogMerger.SymLoyal
