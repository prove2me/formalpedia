-- Prove2me | Theorems.Thm_Arxiv2507_18491_psi_tilde_reaction_decomposition
-- name    : Arxiv2507_18491.psi_tilde_reaction_decomposition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:59:07.065553+00:00
-- url     : https://prove2.me/theorems/15d003c0-fae4-4b1b-99a5-3dd683e145a6
-- title:
--   Eq. (3.8): the reaction decomposition of $\tilde\psi_\ell$
-- statement:
--   Let the layered medium have $L+1$ layers with interfaces $d_0>\dots>d_{L-1}$, frequency $\omega>0$, and $\varepsilon_j,\mu_j>0$. Let the target height $z$ lie in layer $\ell$ and the source height $z'$ lie in layer $\ell'$. Fix $k_\rho\ge0$ with $k_{\ell'z}\neq0$. Take density values $\psi^{\ast\star}_{\ell\ell'}(k_\rho)$ and a free-space part $\psi^f(z,\cdot)$, differentiable at $z'$ when $\ell=\ell'$, and let
--   $$\psi_\ell(k_\rho,z,z')=\delta_{\ell\ell'}\psi^f(z,z')-\frac{1}{2\omega\mu_{\ell'}k_{\ell'z}}\sum_{\ast,\star\in\{\uparrow,\downarrow\}}\psi^{\ast\star}_{\ell\ell'}(k_\rho)Z^{\ast\star}_{\ell\ell'}(k_\rho,z,z').$$
--   Then $\tilde\psi_\ell=-\partial_{z'}\psi_\ell$ is given by the third line of (3.8):
--   $$\tilde\psi_\ell(k_\rho,z,z')=-\delta_{\ell\ell'}\partial_{z'}\psi^f(z,z')+\frac{\mathrm i}{2\omega\mu_{\ell'}}\sum_{\ast,\star}s^{\star\star}_{\ell'\ell'}\psi^{\ast\star}_{\ell\ell'}(k_\rho)Z^{\ast\star}_{\ell\ell'}(k_\rho,z,z').$$
--
--   The sign $s^{\star\star}_{\ell'\ell'}$ is $+1$ for $\star=\downarrow$ and $-1$ for $\star=\uparrow$, whatever $\ell$ and $\ell'$ are.
--
--   **Formalization Note** The free-space function $\psi^f$, which the paper omits, and the densities are arbitrary. The decomposition of the first two lines of (3.8) is taken from the paper's references; only its consequence for $\tilde\psi$ is stated. The hypothesis $k_{\ell'z}\neq0$ (that is, $k_\rho\neq k_{\ell'}$) excludes the point where (3.8) divides by zero.
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c031; Section 3.1, eq. (3.8) third line (from the second line and $\tilde\psi=-\partial_{z'}\psi$), with eqs. (3.9)-(3.11), PDF pp. 6-7

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem psi_tilde_reaction_decomposition (omega : ℝ) (epsL muL : ℕ → ℝ) (homega : 0 < omega)
    (heps : ∀ j, 0 < epsL j) (hmu : ∀ j, 0 < muL j) (L : ℕ) (d : ℕ → ℝ)
    (hd : IsInterfaces L d) (l l' : ℕ) (krho : ℝ) (hkrho : 0 ≤ krho)
    (hkz : vkz (waveNum omega epsL muL l') krho ≠ 0)
    (psiD : Dir → Dir → ℝ → ℂ) (psiF : ℝ → ℝ → ℂ) (z z' : ℝ)
    (hz : InLayer L d l z) (hz' : InLayer L d l' z')
    (hF : l = l' → DifferentiableAt ℝ (fun w => psiF z w) z') :
    -deriv (fun w => (if l = l' then (1 : ℂ) else 0) * psiF z w
        + psiReac omega (waveNum omega epsL muL) muL d l l' psiD krho z w) z' =
      -(if l = l' then (1 : ℂ) else 0) * deriv (fun w => psiF z w) z'
        + Complex.I / (2 * (omega : ℂ) * (muL l' : ℂ)) *
          ∑ a : Dir, ∑ b : Dir, (sgnS l' l' b : ℂ) * psiD a b krho *
            Zfun (waveNum omega epsL muL) d l l' a b krho z z' := by sorry

end Arxiv2507_18491
