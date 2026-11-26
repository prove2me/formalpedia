-- Prove2me | Theorems.Thm_CondMat0408017_rre_p_and_s_forms
-- name    : CondMat0408017.rre_p_and_s_forms
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T13:20:18.747937+00:00
-- url     : https://prove2.me/theorems/e27d0edc-fd51-4de1-a6f9-57209c227241
-- title:
--   Eqs. (79)-(80): the reduced Rayleigh equation for $p$ and $s$ polarization
-- statement:
--   Let $\varepsilon$ be complex, $w=\omega/c$, and let $\alpha,\alpha_0$ satisfy $\alpha(q)^2=\varepsilon w^2-q^2$ and $\alpha_0(q)^2=w^2-q^2$. Let $I(\gamma|Q)$ be any function. With the matrix elements $M^\pm_\nu$ of the reduced Rayleigh equation (78) ($\kappa_p=\varepsilon$, $\kappa_s=1$) and $N^\pm_\nu$ of (79b), (80b):
--
--   1. Wherever $\alpha(p)\mp\alpha_0(q)\ne0$,
--   $$M^\pm_p(p|q)=(\varepsilon-1)N^\pm_p(p|q),\qquad M^\pm_s(p|q)=(\varepsilon-1)\frac{\omega^2}{c^2}N^\pm_s(p|q) .$$
--   2. Let $R(q|k)=2\pi\delta(q-k)d(k)+r(q,k)$, and let $\varepsilon\ne1$, $\alpha(p)\pm\alpha_0(k)\ne0$. Then the reduced Rayleigh equation $\int\frac{dq}{2\pi}M^+_\nu(p|q)R(q|k)=M^-_\nu(p|k)$ holds if and only if $\int\frac{dq}{2\pi}N^+_\nu(p|q)R(q|k)=N^-_\nu(p|k)$ holds (eqs. 79a, 80a). For $s$ polarization this needs $\omega/c\ne0$.
--
--   **Formalization Note** The paper prints the right-hand sides of (78), (79a), (80a) as $M^-(p|q)$, $N^-(p|q)$; since $q$ is the integration variable, $(p|k)$ is meant and is used here. The factor $I(\alpha(p)\mp\alpha_0(q)|p-q)$ is common to $M$ and $N$, so the identities hold for any $I$. In part 2 the integral over the regular part is a Lebesgue integral. The identity of part 1 fails only where $\alpha(p)=\pm\alpha_0(q)$, which for fixed $p$ is at most two values of $q$.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c011; Sec. III.E.3, eqs. (Theory:RRE-p), (Theory:RRE-s) [(79)-(80)] with footnotes, from eq. (Theory:RRE) [(78)], PDF pp. 25-26

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem rre_p_and_s_forms (eps : ℂ) (wv : ℝ) (α α0 : ℝ → ℂ)
    (hα : ∀ q, α q ^ 2 = eps * wv ^ 2 - q ^ 2) (hα0 : ∀ q, α0 q ^ 2 = wv ^ 2 - q ^ 2)
    (I0 : ℂ → ℝ → ℂ) :
    (∀ sgn : ℂ, (sgn = 1 ∨ sgn = -1) → ∀ p q : ℝ, α p - sgn * α0 q ≠ 0 →
      rreM eps sgn p q (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q) =
          (eps - 1) * (rreNp sgn p q (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q)) ∧
        rreM 1 sgn p q (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q) =
          (eps - 1) * (wv : ℂ) ^ 2 * (rreNs sgn (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q))) ∧
    (∀ (R : DKernel) (p k : ℝ), eps ≠ 1 → α p - α0 k ≠ 0 → α p + α0 k ≠ 0 →
      (DKernel.applyLeft
            (fun p q => rreM eps 1 p q (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k =
          rreM eps (-1) p k (α p) (α0 k) * I0 (α p + α0 k) (p - k) ↔
        DKernel.applyLeft
            (fun p q => rreNp 1 p q (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k =
          rreNp (-1) p k (α p) (α0 k) * I0 (α p + α0 k) (p - k)) ∧
      (wv ≠ 0 →
        (DKernel.applyLeft
              (fun p q => rreM 1 1 p q (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k =
            rreM 1 (-1) p k (α p) (α0 k) * I0 (α p + α0 k) (p - k) ↔
          DKernel.applyLeft
              (fun p q => rreNs 1 (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k =
            rreNs (-1) (α p) (α0 k) * I0 (α p + α0 k) (p - k)))) := by sorry

end CondMat0408017
