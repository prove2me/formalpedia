-- Prove2me | Theorems.Thm_Arxiv1801_00461_conductivity_decomposition_frequency_space
-- name    : Arxiv1801_00461.conductivity_decomposition_frequency_space
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:09:35.394289+00:00
-- url     : https://prove2.me/theorems/338c983d-7836-4d4c-bb53-06ce9aeda891
-- title:
--   Eqs. (22)-(24): the conductivity in frequency space and its high-frequency limit
-- statement:
--   Let $\sigma_\infty$ and $\sigma_\infty\bar\Delta_e$ be integrable on $(0,\infty)$, with $\bar\Delta_e$ not identically zero. Let $E$ be an integrable field. Put $\sigma_e=\sigma_\infty(1+\bar\Delta_e)$ (eq. (21)) and $j(t)=\int_0^\infty\sigma_e(\tau)E(t-\tau)\,d\tau$ (eq. (22)). Then for every real $\omega$
--
--   $$\hat j(\omega)=\Big[\sigma_\infty(\omega)+\int_0^\infty\sigma_\infty(\tau)\bar\Delta_e(\tau)e^{-i\omega\tau}d\tau\Big]\hat E(\omega)\quad(23),\qquad\sigma_e(\omega)=\sigma_\infty(\omega)+\int_0^\infty\sigma_\infty(\tau)\bar\Delta_e(\tau)e^{-i\omega\tau}d\tau\quad(24).$$
--
--   Here $\sigma_\infty(\omega)$ and $\sigma_e(\omega)$ are the one-sided transforms, and $\hat j$, $\hat E$ are the transforms over the whole time axis. The integral in (24) tends to $0$ as $\omega\to+\infty$, so $\sigma_e(\omega)-\sigma_\infty(\omega)\to0$.
--
--   **Formalization Note** The fields are scalar (one Cartesian component of an isotropic medium). In this statement $\sigma_\infty$ is an integrable function, so that $\sigma_\infty(\omega)$ is its transform. The vanishing of the integral, which the paper imposes as a property of the decomposition, follows for integrable kernels.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c027; Sec. 2.3.3, eqs. (21)-(24), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem conductivity_decomposition_frequency_space (sigmaInf DeltaE E : ℝ → ℝ)
    (hInf : IntegrableOn sigmaInf (Set.Ioi 0))
    (hint : IntegrableOn (fun t => sigmaInf t * DeltaE t) (Set.Ioi 0)) (hDelta : ∃ t, DeltaE t ≠ 0)
    (hE : Integrable E) :
    (∀ ω : ℝ, fourierFT (freeCurrent sigmaInf DeltaE E) ω =
        (causalFT sigmaInf ω + condDev (fun t => sigmaInf t * DeltaE t) ω) * fourierFT E ω) ∧
    (∀ ω : ℝ, causalFT (condKernel sigmaInf DeltaE) ω =
        causalFT sigmaInf ω + condDev (fun t => sigmaInf t * DeltaE t) ω) ∧
    Tendsto (fun ω : ℝ => condDev (fun t => sigmaInf t * DeltaE t) ω) atTop (𝓝 0) ∧
    Tendsto (fun ω : ℝ => causalFT (condKernel sigmaInf DeltaE) ω - causalFT sigmaInf ω) atTop
      (𝓝 0) := by sorry

end Arxiv1801_00461
