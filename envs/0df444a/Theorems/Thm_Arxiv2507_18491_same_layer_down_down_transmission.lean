-- Prove2me | Theorems.Thm_Arxiv2507_18491_same_layer_down_down_transmission
-- name    : Arxiv2507_18491.same_layer_down_down_transmission
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:01:46.996053+00:00
-- url     : https://prove2.me/theorems/47e63867-16c9-451e-9d38-6a444b6e7504
-- title:
--   Section 3.2: same-layer $\downarrow\downarrow$ component, transmission distance and decay
-- statement:
--   Let the layered medium be as above, and let layer $\ell$ be bounded by interfaces on both sides ($1\le\ell\le L-1$). Let the target height $z$ and the source height $z'$ both lie in layer $\ell$. For the component $\downarrow\downarrow$, the effective target location is $\tau_{\ell-1}(\boldsymbol r)$ and the equivalent polarization source is $\tau_\ell(\boldsymbol r')$. Their vertical distance $\tau_{\ell-1}(z)-\tau_\ell(z')=2(d_{\ell-1}-d_\ell)-(z-z')$ is positive, and
--   $$Z^{\downarrow\downarrow}_{\ell\ell}(k_\rho,z,z')\sim e^{-k_\rho(\tau_{\ell-1}(z)-\tau_\ell(z'))}\qquad(k_\rho\to+\infty).$$
--
--   **Formalization Note** "$\sim$" is asymptotic equivalence. The physical interpretation (waves with at least two reflections) is not formalized.
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c006; Section 3.2, unnumbered display after the discussion of Fig. 3.1, with eqs. (3.9), (3.21), (3.22), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem same_layer_down_down_transmission (omega : ℝ) (epsL muL : ℕ → ℝ) (homega : 0 < omega)
    (heps : ∀ j, 0 < epsL j) (hmu : ∀ j, 0 < muL j) (L : ℕ) (d : ℕ → ℝ)
    (hd : IsInterfaces L d) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l + 1 ≤ L) (z z' : ℝ)
    (hz : InLayer L d l z) (hz' : InLayer L d l z') :
    effZ d l l false false z = refl d (l - 1) z ∧ polZ d l l false z' = refl d l z' ∧
    0 < refl d (l - 1) z - refl d l z' ∧
    Asymptotics.IsEquivalent atTop
      (fun krho : ℝ => Zfun (waveNum omega epsL muL) d l l false false krho z z')
      (fun krho : ℝ => ((Real.exp (-(krho * (refl d (l - 1) z - refl d l z'))) : ℝ) : ℂ)) := by sorry

end Arxiv2507_18491
