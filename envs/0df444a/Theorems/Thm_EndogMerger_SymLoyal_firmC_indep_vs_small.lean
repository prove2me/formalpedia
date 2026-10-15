-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_firmC_indep_vs_small
-- name    : EndogMerger.SymLoyal.firmC_indep_vs_small
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:10.627956+00:00
-- url     : https://prove2.me/theorems/18a698f6-f036-41d0-8c1b-26c5401a8ad3
-- title:
--   Proof of Proposition 3, PDF p. 49 — Π^(0)_C < Π^(BC)_C on Ω^(BC)_1, = on Ω^(BC)_2 and for (1−α)/2 < k < 1−2α
-- statement:
--   Let $0<\alpha<1/3$, $\alpha<k<1-2\alpha$ and $r>0$. Firm $C$'s Table A1 profit without merger, $\Pi^{(0)}_C$, and in the small merger, $\Pi^{(BC)}_C=\Pi^{(BC)}/2$, satisfy
--
--   1. on $\Omega^{(BC)}_1$: $\Pi^{(0)}_C<\Pi^{(BC)}_C$;
--   2. on $\Omega^{(BC)}_2$: $\Pi^{(0)}_C=\Pi^{(BC)}_C$;
--   3. if $(1-\alpha)/2<k$:
--   $$
--   \Pi^{(0)}_C=\Pi^{(BC)}_C=r\alpha .
--   $$
--
--   So condition (2a), a small firm's gain from the small merger, holds only on $\Omega^{(BC)}_1$.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, Appendix H, proof of Proposition 3, PDF p. 49

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting
import Definitions.Def_EndogMerger_SymLoyal_Regions

namespace EndogMerger.SymLoyal
theorem firmC_indep_vs_small (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (OmegaBC₁ α k → piIndepB α k r < piBCB α k r) ∧
    (OmegaBC₂ α k → piIndepB α k r = piBCB α k r) ∧
    ((1 - α) / 2 < k → piIndepB α k r = piBCB α k r) := by sorry
end EndogMerger.SymLoyal
