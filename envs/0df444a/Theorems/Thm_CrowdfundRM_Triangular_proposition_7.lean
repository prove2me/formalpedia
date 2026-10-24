-- Prove2me | Theorems.Thm_CrowdfundRM_Triangular_proposition_7
-- name    : CrowdfundRM.Triangular.proposition_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:28.148362+00:00
-- url     : https://prove2.me/theorems/a0ed2012-1b1d-492c-9d79-7bc6859b8d3c
-- title:
--   Proposition 7, p. 20 — jointly optimal pledge level and campaign duration under right-triangular valuations, without herding (k = r) and for the herding proxy R_h
-- statement:
--   Consider a campaign satisfying the standing assumptions. Let $x^*_0$ and $x^*_1$ be the constants (34) and (35), and maximize over the feasible set of (18), $0<p\le\bar v$, $0\le T\le\frac1r\ln(\bar v/p)$.
--
--   1. **(a), mode 0.** If $k=r$, $\Lambda_h=0$ and the independent valuations are right-triangular with mode $v^m_i=0$, the unique maximizer of $\pi(p,T)=p\,n(p,T)$ is
--   $$(p^*,T^*)=\left(\bar v\,\frac{x^*_0-\sqrt{x^*_0}+1}{(x^*_0)^2+x^*_0+1},\ \frac1r\ln x^*_0\right).\qquad(36)$$
--   2. **(a), mode $\bar v$.** If $k=r$, $\Lambda_h=0$ and the independent valuations are right-triangular with mode $v^m_i=\bar v$, the unique maximizer of $\pi$ is
--   $$(p^*,T^*)=\left(\bar v\,\frac1{\sqrt{1+x^*_1+(x^*_1)^2}},\ \frac1r\ln x^*_1\right).\qquad(37)$$
--   3. **(b), mode 0.** If the herding valuations are right-triangular with mode $v^m_h=0$, then the equation
--   $$\ln\frac1\beta=\frac32\Bigl(\beta-\frac43\Bigr)^2-\frac16\qquad(39)$$
--   has exactly one solution $\beta^*\in(0,1)$, and the unique maximizer of $R_h(p,T)=p\int_0^T\bar F_h(pe^{ry})dy$ (27) is $(p^*,T^*)=\bigl(\beta^*\bar v,\ \frac1r\ln\frac1{\beta^*}\bigr)$ (38).
--   4. **(b), mode $\bar v$.** If the herding valuations are right-triangular with mode $v^m_h=\bar v$, then $we^w=-3e^{-3}$ has exactly one solution $w^*\in(-1,0)$ (the principal Lambert value $W(-3/e^3)$), and the unique maximizer of $R_h$ is
--   $$(p^*,T^*)=\left(\sqrt{\frac{-w^*}{3}}\,\bar v,\ \frac1r\ln\sqrt{\frac{3}{-w^*}}\right).\qquad(40)$$
--
--   This is the paper's flexible-setting result for triangular valuations: closed-form joint optima in the four limiting regimes (independent- or herding-dominated, low or high valuation mode).
--
--   **Formalization Note** Part (a) assumes $k=r$ and $\Lambda_h=0$ and constrains $\bar F_i$; part (b) maximizes the explicit proxy (27), needs neither, and constrains $\bar F_h$. The printed decimals (including the incorrect $0.191\bar v$ in (36); the exact expression is $\approx0.198\bar v$) are not part of the statement. Equation (39) also has the root $\beta=1$, so uniqueness is posed on $(0,1)$. The paper prints (40) as $\bigl(-i\sqrt{W(-3/e^3)/3}\,\bar v,\ \frac1r\ln(i\sqrt{3/W(-3/e^3)})\bigr)$ with the Lambert $W$ function; since $W(-3/e^3)<0$, $-i\sqrt{W/3}=\sqrt{-W/3}$ and the intended duration is $\frac1r\ln\sqrt{3/(-W)}$, which is the real form stated here, with $W(-3/e^3)$ characterized as the unique $w\in(-1,0)$ with $we^w=-3e^{-3}$ (the other real solution, $w=-3$, is excluded). "Optimal" is stated as: feasible, maximal, and the unique maximizer.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), p. 20, Proposition 7, (34)–(40)

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

namespace CrowdfundRM.Triangular
theorem proposition_7 (M : Campaign) (hM : M.Standing) :
    (M.k = M.r → M.Lh = 0 → M.Fbi = triBar0 M.vbar →
      IsUniqueMaxOn₂ M.revenue M.Feasible
        (M.vbar * ((x0 - Real.sqrt x0 + 1) / (x0 ^ 2 + x0 + 1))) (Real.log x0 / M.r)) ∧
    (M.k = M.r → M.Lh = 0 → M.Fbi = triBar1 M.vbar →
      IsUniqueMaxOn₂ M.revenue M.Feasible
        (M.vbar * (1 / Real.sqrt (1 + x1 + x1 ^ 2))) (Real.log x1 / M.r)) ∧
    (M.Fbh = triBar0 M.vbar →
      (∃! β : ℝ, 0 < β ∧ β < 1 ∧ Real.log (1 / β) = 3 / 2 * (β - 4 / 3) ^ 2 - 1 / 6) ∧
      ∀ β : ℝ, 0 < β → β < 1 → Real.log (1 / β) = 3 / 2 * (β - 4 / 3) ^ 2 - 1 / 6 →
        IsUniqueMaxOn₂ M.Rh M.Feasible (β * M.vbar) (Real.log (1 / β) / M.r)) ∧
    (M.Fbh = triBar1 M.vbar →
      (∃! w : ℝ, -1 < w ∧ w < 0 ∧ w * Real.exp w = -3 * Real.exp (-3)) ∧
      ∀ w : ℝ, -1 < w → w < 0 → w * Real.exp w = -3 * Real.exp (-3) →
        IsUniqueMaxOn₂ M.Rh M.Feasible
          (Real.sqrt (-w / 3) * M.vbar) (Real.log (Real.sqrt (3 / -w)) / M.r)) := by sorry
end CrowdfundRM.Triangular
