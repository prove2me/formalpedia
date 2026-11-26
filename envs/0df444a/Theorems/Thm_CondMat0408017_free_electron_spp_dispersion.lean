-- Prove2me | Theorems.Thm_CondMat0408017_free_electron_spp_dispersion
-- name    : CondMat0408017.free_electron_spp_dispersion
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:25:54.589801+00:00
-- url     : https://prove2.me/theorems/9a2a74be-b6ab-5b7e-b7b1-7d0e1a6b26f6
-- title:
--   Eqs. (21)-(22): the SPP dispersion curve of a free-electron metal, its limits, and its position right of the light line
-- statement:
--   Let vacuum ($\varepsilon_+=1$) lie above a free-electron metal with $\varepsilon_-(\omega)=\varepsilon_\infty(1-\omega_p^2/\omega^2)$, where $\varepsilon_\infty>0$, $\omega_p>0$ and $c>0$. Let
--
--   $$\omega_{sp}(k)=\Big[\tfrac12\Big(\tfrac{k^2c^2}{\varepsilon_\infty}(1+\varepsilon_\infty)+\omega_p^2\Big)-\tfrac12\sqrt{\Big(\tfrac{k^2c^2}{\varepsilon_\infty}(1+\varepsilon_\infty)+\omega_p^2\Big)^2-4k^2c^2\omega_p^2}\,\Big]^{1/2}$$
--
--   (eq. 21). Then:
--
--   1. For $k>0$ and $\omega>0$, a $p$-polarized SPP of wave number $k$ and frequency $\omega$ exists at the vacuum-metal interface if and only if $\omega=\omega_{sp}(k)$.
--   2. $\omega_{sp}(k)/(kc)\to1$ as $k\to0^+$, and $\omega_{sp}(k)\to\sqrt{\varepsilon_\infty/(\varepsilon_\infty+1)}\,\omega_p$ as $k\to\infty$ (eq. 22).
--   3. $\omega_{sp}(k)<kc$ for every $k>0$: the dispersion curve lies to the right of the light line $\omega=kc$, so light incident on the planar interface, whose wave number along the surface is at most $\omega/c$, cannot excite an SPP.
--
--   **Formalization Note** "Exists" means the definition from Sec. II.D.1: $\beta_\pm$ are real and positive and the boundary conditions with $\kappa^\pm=\varepsilon_\pm$ have a non-zero solution. Item 1 therefore says that (21) is the inverse of the dispersion relation (19) and that it picks out exactly the physical root. The paper's "$\omega_{sp}\to kc$ as $k\to0$" is read as the ratio tending to $1$, since both sides tend to $0$. The paper writes $\varepsilon_\infty(\omega)$ but uses it as a constant. The paper shows item 3 for $\varepsilon_\infty=1$ in Fig. 3; here it is stated for every $\varepsilon_\infty>0$.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c036; Sec. II.D.2, eqs. (Elmag:SPP-free-metal), (Eq:Elmag:assymp) [(21)-(22)] and Fig. 3, PDF pp. 10-11

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem free_electron_spp_dispersion (epsInf ωp c : ℝ) (he : 0 < epsInf) (hp : 0 < ωp)
    (hc : 0 < c) :
    (∀ k ω : ℝ, 0 < k → 0 < ω →
      (IsPlanarSPP 1 (freeElectronEps epsInf ωp ω) k ω c ↔ ω = omegaSP epsInf ωp c k)) ∧
    Tendsto (fun k => omegaSP epsInf ωp c k / (k * c)) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (omegaSP epsInf ωp c) atTop (𝓝 (Real.sqrt (epsInf / (epsInf + 1)) * ωp)) ∧
    ∀ k : ℝ, 0 < k → omegaSP epsInf ωp c k < k * c := by sorry

end CondMat0408017
