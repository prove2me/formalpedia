-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_lemma_3
-- name    : EndogMerger.SymLoyal.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:56.364663+00:00
-- url     : https://prove2.me/theorems/a3a55526-022e-4285-b860-0e5f91e37dbe
-- title:
--   Lemma 3, PDF p. 14 — in {A,B,C}, L^(0) = r(α+s₂)/(1−2α) on Ω^(0)_1 and rα/k on Ω^(0)_2
-- statement:
--   Consider the independent structure $\{A,B,C\}$ with $0<\alpha<1/3$, $\alpha<k<1-2\alpha$ and $r>0$, and let $L^{(0)}$, $\Pi^{(0)}_A$ and $\Pi^{(0)}_B=\Pi^{(0)}_C$ be the Table A1 quantities. Let $\alpha^{(0)}_1\in(0,1/3)$ be the root of $-43\alpha^3+43\alpha^2-13\alpha+1=0$.
--
--   1. If $(\alpha,k)\in\Omega^{(0)}_1$, i.e. $0<\alpha<\alpha^{(0)}_1$ and $k^{(0)}_1(\alpha)<k<k^{(0)}_2(\alpha)$, then
--   $$
--   L^{(0)}=\frac{r(\alpha+s_2)}{1-2\alpha},\qquad \Pi^{(0)}_A=r(\alpha+s_2),\qquad \Pi^{(0)}_B=\Pi^{(0)}_C=\frac{r(\alpha+s_2)k}{1-2\alpha}.
--   $$
--   2. If $(\alpha,k)\in\Omega^{(0)}_2$ (outside $\Omega^{(0)}_1$), then
--   $$
--   L^{(0)}=\frac{r\alpha}{k},\qquad \Pi^{(0)}_A=\frac{r\alpha(1-2\alpha)}{k},\qquad \Pi^{(0)}_B=\Pi^{(0)}_C=r\alpha.
--   $$
--
--   The lemma identifies where firm $A$, rather than the small firms, sets the lower bound of the price support in the independent structure.
--
--   **Formalization Note** The paper defines $\alpha^{(0)}_1$ by $k^{(0)}_1(\alpha^{(0)}_1)=k^{(0)}_2(\alpha^{(0)}_1)$, i.e. as the root of the cubic under the square root; it is passed as a parameter `α₁` with the hypotheses $0<\alpha_1<1/3$ and $c_0(\alpha_1)=0$, which determine it uniquely. $0<\alpha$ and $r>0$ are added as in Lemma 5.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, PDF p. 14, Lemma 3 and footnote 12; proof PDF p. 46

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting
import Definitions.Def_EndogMerger_SymLoyal_Regions

namespace EndogMerger.SymLoyal
theorem lemma_3 (α₁ : ℝ) (hα₁ : 0 < α₁ ∧ α₁ < 1 / 3 ∧ cubic0 α₁ = 0)
    (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (Omega0₁ α₁ α k →
      L0 α k r = r * (α + s2 α k) / (1 - 2 * α) ∧
      piIndepA α k r = r * (α + s2 α k) ∧
      piIndepB α k r = r * (α + s2 α k) * k / (1 - 2 * α)) ∧
    (Omega0₂ α₁ α k →
      L0 α k r = r * α / k ∧
      piIndepA α k r = r * α * (1 - 2 * α) / k ∧
      piIndepB α k r = r * α) := by sorry
end EndogMerger.SymLoyal
