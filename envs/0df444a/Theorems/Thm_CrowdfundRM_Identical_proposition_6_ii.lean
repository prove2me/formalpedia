-- Prove2me | Theorems.Thm_CrowdfundRM_Identical_proposition_6_ii
-- name    : CrowdfundRM.Identical.proposition_6_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:52.681899+00:00
-- url     : https://prove2.me/theorems/299b361b-8ab3-4537-80b9-333802160649
-- title:
--   Proposition 6(ii), p. 19 — identical valuations, v_i > v_h, weak herding and v_i/v_h above threshold (33): the optimum is p* = v_i (r/(k+r))^{r/k}, T* = (1/r) ln(v_i/p*)
-- statement:
--   Consider the crowdfunding model with standing assumptions, where every independent backer values the project at $v_i$ and every herding backer at $v_h$, with $0<v_i\le\bar v$ and $0<v_h\le\bar v$, and with $\Lambda_h>0$, $q>0$. The creator chooses a pledge level $p$ and a duration $T$ to maximize the revenue $\pi(p,T)=p\,n(p,T)$ over the set
--
--   $$0<p\le\bar v,\qquad 0\le T\le\frac1r\ln\frac{\bar v}{p},\qquad T\le\frac1r\ln\frac{v_i}{p}.$$
--
--   Suppose $v_i>v_h$, and define, as in (32) and (33),
--
--   $$\delta=\frac{\Lambda_h q v_h}{r},\quad a=\frac{k}{\Lambda_h q},\quad b=\frac{\Lambda_h q}{r},$$
--
--   $$X=e^{bv_h/e}\,\frac1{4a}\Big(\frac kr v_h e^{-2}+0.5\,b v_h^2e^{-3}+2a+v_h\Big)+\frac1a\Big(\frac kr(v_h+a)+a\Big).$$
--
--   If $\delta<1$ and
--
--   $$\frac{v_i}{v_h}>\Big(\frac{X}{1-\delta}\Big)^{r/k},$$
--
--   then the unique optimal pledge level and duration are
--
--   $$p^*=v_i\Big(\frac{r}{k+r}\Big)^{r/k},\qquad T^*=\frac1r\ln\frac{v_i}{p^*}.$$
--
--   These are the optimal decisions of a campaign without herding backers: when herding is weak and independent backers value the project much more than herding ones, the creator sets the pledge above what herding backers will pay and ignores them.
--
--   **Formalization Note.** The paper prints $T^*=\frac1r\ln(v_i/\bar p)$ with an undefined $\bar p$; it is read as $p^*$. The duration is stated as $\frac1r\ln(v_i/p^*)$, which equals $\frac1k\ln\frac{k+r}{r}$. "The optimal" is read as the unique maximizer. $\Lambda_h>0$ and $q>0$ are added because $a$ and $b$ divide by $\Lambda_h q$. In (33) the factors $e^{bv_h/e}$ and $1/(4a)$ multiply only the first bracket, following the rendered page. The other added hypotheses are the standing assumptions and $p>0$ in the feasible set.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), p. 19, Proposition 6(ii), (32)–(33)

import Mathlib
import Definitions.Def_CrowdfundRM_Identical_Setting

namespace CrowdfundRM.Identical

theorem proposition_6_ii (M : Campaign) (hM : M.Standing) (vi vh : ℝ) (hv : IdenticalVals M vi vh)
    (hLh : 0 < M.Lh) (hq : 0 < M.q) (hlt : vh < vi) (hδ : δ6 M vh < 1)
    (hX : (Xthr M vh / (1 - δ6 M vh)) ^ (M.r / M.k) < vi / vh) :
    CrowdfundRM.Triangular.IsUniqueMaxOn₂ (revenue M) (Feasible6 M vi)
      (vi * (M.r / (M.k + M.r)) ^ (M.r / M.k))
      (1 / M.r * Real.log (vi / (vi * (M.r / (M.k + M.r)) ^ (M.r / M.k)))) := by sorry

end CrowdfundRM.Identical
