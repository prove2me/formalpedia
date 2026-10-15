-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_lemma_4
-- name    : EndogMerger.SymLoyal.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:54.763225+00:00
-- url     : https://prove2.me/theorems/e8224574-2b4a-41cf-8a37-d23b8f1adc0e
-- title:
--   Lemma 4, PDF p. 15 — in {A,BC}, L^(BC) = r(α+s₃)/(1−2α), rα/k, 2rα/(1−α) on Ω^(BC)_1, Ω^(BC)_2, Ω^(BC)_3
-- statement:
--   Consider the small merger structure $\{A,BC\}$ with $0<\alpha<1/3$, $\alpha<k<1-2\alpha$ and $r>0$, and let $L^{(BC)}$, $\Pi^{(BC)}_A$, $\Pi^{(BC)}$ be the Table A1 lower bound of price support, firm $A$ profit and merged-entity profit. With $s_3=(1-3\alpha)(1-2k/(1-\alpha))$:
--
--   1. on $\Omega^{(BC)}_1$:
--   $$
--   L^{(BC)}=\frac{r(\alpha+s_3)}{1-2\alpha},\quad \Pi^{(BC)}_A=r(\alpha+s_3),\quad \Pi^{(BC)}=\frac{2r(\alpha+s_3)k}{1-2\alpha};
--   $$
--   2. on $\Omega^{(BC)}_2$: $L^{(BC)}=r\alpha/k$, $\Pi^{(BC)}_A=r\alpha(1-2\alpha)/k$, $\Pi^{(BC)}=2r\alpha$;
--   3. on $\Omega^{(BC)}_3$: $L^{(BC)}=2r\alpha/(1-\alpha)$, $\Pi^{(BC)}_A=2r\alpha(1-2\alpha)/(1-\alpha)$, $\Pi^{(BC)}=2r\alpha$.
--
--   The lemma resolves the maximum in Table A1's small-merger column; region $\Omega^{(BC)}_1$ is the only place where a small firm gains from the small merger.
--
--   **Formalization Note** $0<\alpha$ and $r>0$ are added as in Lemma 5. $\alpha^{(BC)}_1=(11-\sqrt{17})/52$ is the closed form from the proof of Lemma 4. Part 1 implicitly contains $k^{(BC)}_2(\alpha)<(1-2\alpha)^2/(2-5\alpha)$ on $0<\alpha<\alpha^{(BC)}_1$, so that $\Omega^{(BC)}_1$ lies in Table A1's first row.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, PDF p. 15, Lemma 4 and footnote 13; proof PDF p. 47

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting
import Definitions.Def_EndogMerger_SymLoyal_Regions

namespace EndogMerger.SymLoyal
theorem lemma_4 (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (OmegaBC₁ α k →
      LBC α k r = r * (α + s3 α k) / (1 - 2 * α) ∧
      piBCA α k r = r * (α + s3 α k) ∧
      piBC α k r = 2 * r * (α + s3 α k) * k / (1 - 2 * α)) ∧
    (OmegaBC₂ α k →
      LBC α k r = r * α / k ∧
      piBCA α k r = r * α * (1 - 2 * α) / k ∧
      piBC α k r = 2 * r * α) ∧
    (OmegaBC₃ α k →
      LBC α k r = 2 * r * α / (1 - α) ∧
      piBCA α k r = 2 * r * α * (1 - 2 * α) / (1 - α) ∧
      piBC α k r = 2 * r * α) := by sorry
end EndogMerger.SymLoyal
