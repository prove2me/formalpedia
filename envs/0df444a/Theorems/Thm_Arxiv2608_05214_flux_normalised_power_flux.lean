-- Prove2me | Theorems.Thm_Arxiv2608_05214_flux_normalised_power_flux
-- name    : Arxiv2608_05214.flux_normalised_power_flux
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T19:19:05.146672+00:00
-- url     : https://prove2.me/theorems/b5e8fccc-ffcb-5995-8fee-5bfdf9c61bbb
-- title:
--   Eq. (C-6): flux-normalised one-way fields carry the vertical power flux
-- statement:
--   Let $\omega,\rho,k_{x_3}$ be any real numbers with $k_{x_3}/(\omega\rho)>0$ ($k_{x_3}$ is a free real parameter, not tied to eq. (C-7); this covers the real vertical wavenumber of a propagating mode). For complex amplitudes $\hat P,\hat V_3$ let $\hat P^\pm=\frac12\hat P\pm\frac{\omega\rho}{2k_{x_3}}\hat V_3$ and $\hat Q^\pm=\sqrt{k_{x_3}/(\omega\rho)}\,\hat P^\pm$. Then
--
--   $$\operatorname{Re}\{\hat P^*\hat V_3\}=\frac{k_{x_3}}{\omega\rho}\big(|\hat P^+|^2-|\hat P^-|^2\big)=|\hat Q^+|^2-|\hat Q^-|^2,$$
--
--   because the cross terms are purely imaginary. So the flux-normalised fields carry the vertical acoustic power flux.
--
--   **Formalization Note** The vertical power flux is taken to be $\operatorname{Re}\{\hat P^*\hat V_3\}$. The paper writes 'equals' in Appendix C and 'proportional to' in Section II-B; the time-averaged intensity has an extra factor $\frac12$.
-- source:
--   H. A. Oyekan, Marchenko Theory, Algorithms, and Applications: A Review, arXiv:2608.05214v1 (2026), claim c023; Appendix C-A, eq. (C-6) and the following sentence, PDF p. 32

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Arxiv2608_05214

theorem flux_normalised_power_flux (omega ρ k : ℝ) (hk : 0 < k / (omega * ρ)) (P V : ℂ) :
    (starRingEnd ℂ P * V).re =
        k / (omega * ρ) * (‖downgoingP omega ρ k P V‖ ^ 2 - ‖upgoingP omega ρ k P V‖ ^ 2) ∧
    ‖fluxNormalised omega ρ k (downgoingP omega ρ k P V)‖ ^ 2
        - ‖fluxNormalised omega ρ k (upgoingP omega ρ k P V)‖ ^ 2 = (starRingEnd ℂ P * V).re := by sorry

end Arxiv2608_05214
