-- Prove2me | Theorems.Thm_Arxiv2507_18491_reaction_components_spectral
-- name    : Arxiv2507_18491.reaction_components_spectral
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:00:09.271391+00:00
-- url     : https://prove2.me/theorems/85448cfb-59e4-57dc-879e-f1fded4459a2
-- title:
--   Eqs. (3.12)-(3.14): the spectral reaction field components
-- statement:
--   Let the layered medium be as above, with $z$ in layer $\ell$ and $z'$ in layer $\ell'$. Fix $(k_x,k_y)$ with $k_\rho=\sqrt{k_x^2+k_y^2}>0$ and $k_{\ell'z}\neq0$. Take densities $\phi^{\ast\star}_{\ell\ell'}$ and $\psi^{\ast\star}_{\ell\ell'}$. Insert into the spectral formula (3.3) the reaction parts of (3.8):
--   $$\phi=-\frac{1}{2\omega k_{\ell'z}}\sum_{\ast,\star}\phi^{\ast\star}_{\ell\ell'}Z^{\ast\star}_{\ell\ell'},\qquad\psi=-\frac{1}{2\omega\mu_{\ell'}k_{\ell'z}}\sum_{\ast,\star}\psi^{\ast\star}_{\ell\ell'}Z^{\ast\star}_{\ell\ell'},\qquad\tilde\psi=-\partial_{z'}\psi.$$
--   The result is the sum of the four reaction components (3.12)-(3.13):
--   $$\widehat{\boldsymbol G}_E^{\rm reac}=\sum_{\ast,\star\in\{\uparrow,\downarrow\}}\mathrm i\frac{Z^{\ast\star}_{\ell\ell'}(k_\rho,z,z')}{2k_{\ell'z}}\Theta^{\ast\star}_{\ell\ell'}(k_x,k_y),$$
--   where $\Theta^{\ast\star}_{\ell\ell'}$ are the matrices (3.14).
--
--   **Formalization Note** By linearity, (3.3) splits into a free-space part and a reaction part. The paper identifies the free-space part with $\delta_{\ell\ell'}\widehat{\boldsymbol G}^f_E$ without giving $\phi^f$ and $\psi^f$, so only the reaction part is stated. The term $\boldsymbol\delta$ of (3.3) belongs to the free-space part and is omitted.
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c032; Section 3.1, eqs. (3.12)-(3.14) from eqs. (3.3) and (3.8), PDF pp. 7-8

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem reaction_components_spectral (omega : ℝ) (epsL muL : ℕ → ℝ) (homega : 0 < omega)
    (heps : ∀ j, 0 < epsL j) (hmu : ∀ j, 0 < muL j) (L : ℕ) (d : ℕ → ℝ)
    (hd : IsInterfaces L d) (l l' : ℕ) (kx ky : ℝ) (hk0 : 0 < krhoOf kx ky)
    (hkz : vkz (waveNum omega epsL muL l') (krhoOf kx ky) ≠ 0)
    (phiD psiD : Dir → Dir → ℝ → ℂ) (z z' : ℝ)
    (hz : InLayer L d l z) (hz' : InLayer L d l' z') :
    specGE omega (waveNum omega epsL muL l) (muL l) kx ky
        (phiReac omega (waveNum omega epsL muL) d l l' phiD (krhoOf kx ky))
        (psiReac omega (waveNum omega epsL muL) muL d l l' psiD (krhoOf kx ky))
        (fun z₁ z₂ => -deriv (fun w =>
          psiReac omega (waveNum omega epsL muL) muL d l l' psiD (krhoOf kx ky) z₁ w) z₂)
        z z' =
      ∑ a : Dir, ∑ b : Dir,
        GhatReac (waveNum omega epsL muL) muL d l l' a b (phiD a b) (psiD a b) kx ky z z' := by sorry

end Arxiv2507_18491
