-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_lemma_5
-- name    : EndogMerger.SymLoyal.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:18.758727+00:00
-- url     : https://prove2.me/theorems/dda34353-3272-49f0-ab97-ea98ed9efb60
-- title:
--   Lemma 5, PDF p. 16 — in {AB,C}, L^(AB) = r(2α+s₁)/(1−α) on Ω^(AB)_1 and rα/k on Ω^(AB)_2
-- statement:
--   Consider the mixed merger structure $\{AB,C\}$ with $0<\alpha<1/3$, $\alpha<k<1-2\alpha$ and $r>0$, and let $L^{(AB)}$, $\Pi^{(AB)}$, $\Pi^{(AB)}_C$ be the Table A1 lower bound of price support, merged-entity profit and firm $C$ profit.
--
--   1. If $(\alpha,k)\in\Omega^{(AB)}_1$, i.e. $k^{(AB)}_1(\alpha)\le k<1-2\alpha$, then
--   $$
--   L^{(AB)}=\frac{r(2\alpha+s_1)}{1-\alpha},\qquad \Pi^{(AB)}=r(2\alpha+s_1),\qquad \Pi^{(AB)}_C=\frac{r(2\alpha+s_1)k}{1-\alpha}.
--   $$
--   2. If $(\alpha,k)\in\Omega^{(AB)}_2$, i.e. $\alpha<k<k^{(AB)}_1(\alpha)$, then
--   $$
--   L^{(AB)}=\frac{r\alpha}{k},\qquad \Pi^{(AB)}=\frac{r\alpha(1-\alpha)}{k},\qquad \Pi^{(AB)}_C=r\alpha.
--   $$
--
--   The lemma resolves the maximum in Table A1's mixed-merger column, telling which entity is more pricing aggressive; the proof of Proposition 3 uses it for every comparison involving firm $C$.
--
--   **Formalization Note** The hypotheses $0<\alpha$ (the paper allows $\alpha=0$ in the model but every region requires $\alpha>0$) and $r>0$ (implicit: $r$ is the reservation value) are added. The Table A1 quantities are defined from the table itself, not from these closed forms.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, PDF p. 16, Lemma 5 and footnote 14; proof PDF p. 47

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting
import Definitions.Def_EndogMerger_SymLoyal_Regions

namespace EndogMerger.SymLoyal
theorem lemma_5 (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (OmegaAB₁ α k →
      LAB α k r = r * (2 * α + s1 α k) / (1 - α) ∧
      piAB α k r = r * (2 * α + s1 α k) ∧
      piABC α k r = r * (2 * α + s1 α k) * k / (1 - α)) ∧
    (OmegaAB₂ α k →
      LAB α k r = r * α / k ∧
      piAB α k r = r * α * (1 - α) / k ∧
      piABC α k r = r * α) := by sorry
end EndogMerger.SymLoyal
