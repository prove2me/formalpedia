-- Prove2me | Theorems.Thm_CondMat0408017_zeroth_order_fresnel
-- name    : CondMat0408017.zeroth_order_fresnel
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T13:21:21.190051+00:00
-- url     : https://prove2.me/theorems/8a6df4db-afac-5eef-a942-86b4a5f42f22
-- title:
--   Eq. (86): the zeroth-order amplitude is specular with the Fresnel coefficients
-- statement:
--   Let $\varepsilon\ne1$ be complex, $w=\omega/c\ne0$, and let $\alpha,\alpha_0$ satisfy $\alpha(q)^2=\varepsilon w^2-q^2$, $\alpha_0(q)^2=w^2-q^2$. Let $R^{(0)}(q|k)=2\pi\delta(q-k)d(k)+r(q,k)$ solve the $n=0$ case of the recurrence (85). Since $\tilde\zeta^{(0)}=2\pi\delta$, this reads
--
--   $$\mathcal N^{+(0)}_\nu(q|q)\,R^{(0)}(q|k)=2\pi\delta(q-k)\,\mathcal N^{-(0)}_\nu(k|k),$$
--
--   that is, $\mathcal N^{+(0)}_\nu(k|k)d(k)=\mathcal N^{-(0)}_\nu(k|k)$ and $\mathcal N^{+(0)}_\nu(q|q)r(q,k)=0$.
--
--   1. ($p$) If $\varepsilon\alpha_0(q)+\alpha(q)\ne0$ for all $q$, then $r=0$ and
--   $$d(k)=R^{(0)}_p(k)=\frac{\varepsilon\alpha_0(k)-\alpha(k)}{\varepsilon\alpha_0(k)+\alpha(k)} .$$
--   2. ($s$) If $\alpha_0(q)+\alpha(q)\ne0$ for all $q$, then $r=0$ and
--   $$d(k)=R^{(0)}_s(k)=\frac{\alpha_0(k)-\alpha(k)}{\alpha_0(k)+\alpha(k)} .$$
--
--   So the zeroth-order amplitude is $R^{(0)}(q|k)=2\pi\delta(q-k)R^{(0)}_\nu(k)$, the planar surface reflects only specularly, and $R^{(0)}_\nu$ are the Fresnel coefficients (eq. 86).
--
--   **Formalization Note** The paper prints $\delta(p-k)$ where $\delta(q-k)$ is meant, and "$(\varepsilon=1)$" where $\varepsilon_0=1$ (vacuum above) is meant. The $\delta$-part and the regular part of the $n=0$ equation are matched separately. The $\mathcal N^{\pm(0)}_\nu(q|q)$ are the $n=0$ expansion coefficients of the previous statement.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c013; Sec. III.F, eqs. (Theory:R-zero), (Theory:Fresnel) [(86)] from eq. (85) at n = 0, PDF p. 27

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem zeroth_order_fresnel (eps : ℂ) (wv : ℝ) (α α0 : ℝ → ℂ)
    (hα : ∀ q, α q ^ 2 = eps * wv ^ 2 - q ^ 2) (hα0 : ∀ q, α0 q ^ 2 = wv ^ 2 - q ^ 2)
    (heps : eps ≠ 1) (hwv : wv ≠ 0) (R : DKernel) :
    ((∀ q, eps * α0 q + α q ≠ 0) →
      (∀ k, rreNpCoeff 1 0 k k (α k) (α0 k) * R.diag k = rreNpCoeff (-1) 0 k k (α k) (α0 k)) →
      (∀ q k, rreNpCoeff 1 0 q q (α q) (α0 q) * R.reg q k = 0) →
      (∀ k, R.diag k = fresnelP eps (α k) (α0 k)) ∧ ∀ q k, R.reg q k = 0) ∧
    ((∀ q, α0 q + α q ≠ 0) →
      (∀ k, rreNsCoeff 1 0 (α k) (α0 k) * R.diag k = rreNsCoeff (-1) 0 (α k) (α0 k)) →
      (∀ q k, rreNsCoeff 1 0 (α q) (α0 q) * R.reg q k = 0) →
      (∀ k, R.diag k = fresnelS (α k) (α0 k)) ∧ ∀ q k, R.reg q k = 0) := by sorry

end CondMat0408017
