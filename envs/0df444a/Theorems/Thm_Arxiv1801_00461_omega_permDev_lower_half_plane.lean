-- Prove2me | Theorems.Thm_Arxiv1801_00461_omega_permDev_lower_half_plane
-- name    : Arxiv1801_00461.omega_permDev_lower_half_plane
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:07:57.771866+00:00
-- url     : https://prove2.me/theorems/f0867a2d-9958-4361-8581-7a16cf74044b
-- title:
--   Eqs. (12)-(13) (as proved): continuation of $\omega\bar\Delta\varepsilon$ to the lower half-plane
-- statement:
--   Let $\varepsilon_o>0$ and let $\chi:(0,\infty)\to\mathbb R$ be integrable. For complex $\omega=\omega'+i\omega''$ put $\bar\Delta\varepsilon(\omega)=\int_0^\infty\varepsilon_o\chi(\tau)e^{-i\omega\tau}d\tau$. Then:
--
--   1. for every $\omega$ with $\omega''\le0$, the integrand $\varepsilon_o\chi(\tau)\,\omega\,e^{-i\omega\tau}$ is integrable on $(0,\infty)$;
--   2. for every $\omega$ with $\omega''\le0$ (eq. (13)),
--   $$\lim_{\delta\to0^+}\int_\delta^{1/\delta}\varepsilon_o\chi(\tau)\,[\omega'+i(\omega''-\delta)]\,e^{-i\omega'\tau}e^{(\omega''-\delta)\tau}\,d\tau=\omega\,\bar\Delta\varepsilon(\omega);$$
--   3. $\omega\mapsto\omega\bar\Delta\varepsilon(\omega)$ is holomorphic in the open lower half-plane $\omega''<0$;
--   4. it is continuous on the closed lower half-plane $\omega''\le0$.
--
--   This is the analytic continuation from which the Hilbert relations (16) are derived.
--
--   **Formalization Note** This is what the argument establishes. Three further sentences of the paper are not included because they are false for integrable $\chi$. (a) The integral tends to zero as $\omega''\to-\infty$: for $\chi=\mathbf 1_{[0,1]}$ one has $\omega\bar\Delta\varepsilon=-i\varepsilon_o(1-e^{-i\omega})\to-i\varepsilon_o$. (b) It diverges for $\omega''>0$: the same $\chi$, which has finite duration as in footnote 3, gives an entire function. (c) It is holomorphic on the real axis: for $\chi(\tau)=(1+\tau)^{-2}$, $\bar\Delta\varepsilon$ contains a term $\omega\log\omega$ at $\omega=0$, so $\omega\bar\Delta\varepsilon$ is not holomorphic there. Continuity up to the real axis (item 4) is what the contour argument uses.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c002; Sec. 2.2.2, eqs. (12)-(13) and the two paragraphs after (13), PDF pp. 5-6

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem omega_permDev_lower_half_plane (eps0 : ℝ) (heps0 : 0 < eps0) (chi : ℝ → ℝ)
    (hchi : IntegrableOn chi (Set.Ioi 0)) :
    (∀ ω : ℂ, ω.im ≤ 0 → IntegrableOn
        (fun τ : ℝ => ((eps0 * chi τ : ℝ) : ℂ) * ω * Complex.exp (-(Complex.I * ω * τ)))
        (Set.Ioi 0)) ∧
    (∀ ω : ℂ, ω.im ≤ 0 → Tendsto (fun δ : ℝ => ∫ τ in Set.Ioo δ (1 / δ),
        ((eps0 * chi τ : ℝ) : ℂ) * (ω - Complex.I * δ) *
          Complex.exp (-(Complex.I * (ω - Complex.I * δ) * τ)))
        (𝓝[>] 0) (𝓝 (ω * permDev eps0 chi ω))) ∧
    DifferentiableOn ℂ (fun ω : ℂ => ω * permDev eps0 chi ω) {ω : ℂ | ω.im < 0} ∧
    ContinuousOn (fun ω : ℂ => ω * permDev eps0 chi ω) {ω : ℂ | ω.im ≤ 0} := by sorry

end Arxiv1801_00461
