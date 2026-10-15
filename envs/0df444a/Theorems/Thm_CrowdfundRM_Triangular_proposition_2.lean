-- Prove2me | Theorems.Thm_CrowdfundRM_Triangular_proposition_2
-- name    : CrowdfundRM.Triangular.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:13.738645+00:00
-- url     : https://prove2.me/theorems/799078ed-baaf-49ec-857c-4e3f16c8f2f0
-- title:
--   Proposition 2, p. 10 — every solution of the herding backers' system (8)–(10) is the closed form (11)–(12)
-- statement:
--   Consider a campaign satisfying the standing assumptions, a pledge level $p$ and a duration $T\ge0$. Let $(n_i,n^p_i,n^l_i)$ solve the independent backers' system (1)–(4) on $[0,T]$ and let $(n^p_h,n^l_h)$ solve the herding backers' system (8)–(10) on $[0,T]$ driven by $n^p_i$ (both in integral form). Then for every $t\in[0,T]$,
--   $$n^p_h(t)=\Lambda_h q p\Bigl(k\hat I\int_0^t d\tau\,e^{\Lambda_h q p\int_\tau^t \bar F_h(pe^{r(T-u)})du}\,\bar F_h(pe^{r(T-\tau)})\int_0^\tau e^{-kx}\bar F_i(pe^{r(T-x)})dx\Bigr)\qquad(11)$$
--   and
--   $$n^l_h(t)=\Lambda_h q p\,k\hat I\int_0^t du\,F_h(pe^{r(T-u)})\Bigl(\int_0^u e^{-kx}\bar F_i(pe^{r(T-x)})dx+\Lambda_h q p\int_0^u d\tau\,e^{\Lambda_h q p\int_\tau^u \bar F_h(pe^{r(T-w)})dw}\,\bar F_h(pe^{r(T-\tau)})\int_0^\tau e^{-kx}\bar F_i(pe^{r(T-x)})dx\Bigr).\qquad(12)$$
--   Conversely, $(n^p_i$ of (5)$,$ (11)$,$ (12)$)$ solve (8)–(10).
--
--   Together with Proposition 1 this gives the total number of pledges $n(p,T)$ in closed form.
--
--   **Formalization Note** The printed (12) lacks the factor $\Lambda_h q p$ that (9) puts in front of the rate, and writes the inner upper limits as $v$ where the outer variable is $u$; read literally it is false whenever $\Lambda_h q p\ne1$. The statement uses the corrected display. $F_h=1-\bar F_h$.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), p. 10, Proposition 2, (8)–(12)

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

namespace CrowdfundRM.Triangular
theorem proposition_2 (M : Campaign) (hM : M.Standing) (p T : ℝ) (hT : 0 ≤ T) :
    (∀ ni np nl nhp nhl : ℝ → ℝ, M.IndepSol p T ni np nl → M.HerdSol p T np nhp nhl →
      ∀ t ∈ Set.Icc 0 T, nhp t = M.nph p T t ∧ nhl t = M.nlh p T t) ∧
    M.HerdSol p T (M.npi p T) (M.nph p T) (M.nlh p T) := by sorry
end CrowdfundRM.Triangular
