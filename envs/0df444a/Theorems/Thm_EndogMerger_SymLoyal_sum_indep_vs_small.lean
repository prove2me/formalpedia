-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_sum_indep_vs_small
-- name    : EndogMerger.SymLoyal.sum_indep_vs_small
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:53.961726+00:00
-- url     : https://prove2.me/theorems/18eb0a28-dbf8-4f47-bbdf-752cbee2e3f2
-- title:
--   Proof of Proposition 3, PDF p. 48 — Π^(0)_A+Π^(0)_B vs Π^(BC)_A+Π^(BC)_B: < on Ω^(BC)_1, = on Ω^(BC)_2, < for k > (1−α)/2
-- statement:
--   Let $0<\alpha<1/3$, $\alpha<k<1-2\alpha$ and $r>0$. Compare the joint Table A1 profit of firms $A$ and $B$ without merger, $\Pi^{(0)}_A+\Pi^{(0)}_B$, with their joint profit in the small merger, $\Pi^{(BC)}_A+\Pi^{(BC)}_B$ (where $\Pi^{(BC)}_B=\Pi^{(BC)}/2$):
--
--   1. on $\Omega^{(BC)}_1$: $\Pi^{(0)}_A+\Pi^{(0)}_B<\Pi^{(BC)}_A+\Pi^{(BC)}_B$;
--   2. on $\Omega^{(BC)}_2$: $\Pi^{(0)}_A+\Pi^{(0)}_B=\Pi^{(BC)}_A+\Pi^{(BC)}_B$;
--   3. if $(1-\alpha)/2<k<1-2\alpha$:
--   $$
--   \Pi^{(0)}_A+\Pi^{(0)}_B<\Pi^{(BC)}_A+\Pi^{(BC)}_B .
--   $$
--
--   **Formalization Note** The paper states part 3 on $\Omega^{(BC)}_3$, which includes $k=(1-\alpha)/2$; there its displayed difference $r\alpha(1-2\alpha)(1-\alpha-2k)/((1-\alpha)k)$ is $0$, so the strict inequality is stated for $k>(1-\alpha)/2$.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, Appendix H, proof of Proposition 3, PDF p. 48

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting
import Definitions.Def_EndogMerger_SymLoyal_Regions

namespace EndogMerger.SymLoyal
theorem sum_indep_vs_small (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (OmegaBC₁ α k →
      piIndepA α k r + piIndepB α k r < piBCA α k r + piBCB α k r) ∧
    (OmegaBC₂ α k →
      piIndepA α k r + piIndepB α k r = piBCA α k r + piBCB α k r) ∧
    ((1 - α) / 2 < k →
      piIndepA α k r + piIndepB α k r < piBCA α k r + piBCB α k r) := by sorry
end EndogMerger.SymLoyal
