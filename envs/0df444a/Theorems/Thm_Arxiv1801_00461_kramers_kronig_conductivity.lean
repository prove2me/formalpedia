-- Prove2me | Theorems.Thm_Arxiv1801_00461_kramers_kronig_conductivity
-- name    : Arxiv1801_00461.kramers_kronig_conductivity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:10:19.21148+00:00
-- url     : https://prove2.me/theorems/d274882e-8d7a-4b05-9103-5ca9babfa3ed
-- title:
--   Eq. (26) (as proved): Kramers-Kronig relations for the conductivity
-- statement:
--   Let $\sigma_\infty,\bar\Delta_e$ be real kernels with $\sigma_\infty\bar\Delta_e$ integrable on $(0,\infty)$, and for complex $\omega=\omega'+i\omega''$ let
--
--   $$\bar\Delta\sigma_e(\omega)=\int_0^\infty\sigma_\infty(\tau)\bar\Delta_e(\tau)e^{-i\omega\tau}d\tau .$$
--
--   Then:
--
--   1. for $\omega''<0$ the integral converges absolutely. It equals $\lim_{\delta\to0^+}\int_\delta^{1/\delta}\sigma_\infty\bar\Delta_e\,e^{-i\omega'\tau}e^{(\omega''-\delta)\tau}d\tau$ (eq. (25)), and it tends to $0$ as $\omega''\to-\infty$ for fixed $\omega'$;
--   2. on the real axis $\bar\Delta\sigma_e'$ is even and $\bar\Delta\sigma_e''$ is odd;
--   3. (eq. (26)) for every real $\omega$, with both principal values existing,
--   $$\bar\Delta\sigma_e''(\omega)=\mathcal H(\bar\Delta\sigma_e')(\omega)=\frac1\pi⨍_{-\infty}^{\infty}\frac{\bar\Delta\sigma_e'(\omega_a)}{\omega_a-\omega}d\omega_a,\qquad\bar\Delta\sigma_e'(\omega)=-\mathcal H(\bar\Delta\sigma_e'')(\omega);$$
--   4. consequently the real part of $\bar\Delta\sigma_e$ on the real axis determines its imaginary part, and conversely: two such kernels whose transforms have the same real part (respectively imaginary part) at every real frequency have the same imaginary part (respectively real part).
--
--   This is the paper's main result: Kramers–Kronig relations for the electric conductivity, analogous to those for the permittivity.
--
--   **Formalization Note** The statement leaves out the paper's sentence that the integral (25) diverges for $\omega''>0$, which is false: a kernel of finite duration, as in footnote 3, gives an entire function. No decay hypothesis is added. For an integrable kernel the transform tends to $0$ uniformly in the closed lower half-plane, which is the vanishing of the large-arc integral that the paper invokes. The principal value uses the coupled truncation $(\delta,1/\delta)$ of Fig. 1.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c007; Sec. 2.3.4, eqs. (25)-(26) and the paragraph after (26), PDF pp. 8-9; restated in Sec. 4, PDF p. 15, and the Abstract, PDF p. 1

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem kramers_kronig_conductivity (sigmaInf DeltaE : ℝ → ℝ)
    (hint : IntegrableOn (fun t => sigmaInf t * DeltaE t) (Set.Ioi 0)) :
    (∀ ω : ℂ, ω.im < 0 → IntegrableOn
        (fun τ : ℝ => ((sigmaInf τ * DeltaE τ : ℝ) : ℂ) * Complex.exp (-(Complex.I * ω * τ)))
        (Set.Ioi 0)) ∧
    (∀ ω : ℂ, ω.im < 0 → Tendsto (fun δ : ℝ => ∫ τ in Set.Ioo δ (1 / δ),
        ((sigmaInf τ * DeltaE τ : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω - Complex.I * δ) * τ)))
        (𝓝[>] 0) (𝓝 (condDev (fun t => sigmaInf t * DeltaE t) ω))) ∧
    (∀ ω' : ℝ, Tendsto (fun y : ℝ => condDev (fun t => sigmaInf t * DeltaE t) ((ω' : ℂ) + y * Complex.I)) atBot (𝓝 0)) ∧
    (∀ ω : ℝ, (condDev (fun t => sigmaInf t * DeltaE t) ((-ω : ℝ) : ℂ)).re = (condDev (fun t => sigmaInf t * DeltaE t) ω).re ∧
      (condDev (fun t => sigmaInf t * DeltaE t) ((-ω : ℝ) : ℂ)).im = -(condDev (fun t => sigmaInf t * DeltaE t) ω).im) ∧
    (∀ ω : ℝ, HasHilbert (fun a => (condDev (fun t => sigmaInf t * DeltaE t) a).re) ω (condDev (fun t => sigmaInf t * DeltaE t) ω).im ∧
      HasHilbert (fun a => (condDev (fun t => sigmaInf t * DeltaE t) a).im) ω (-(condDev (fun t => sigmaInf t * DeltaE t) ω).re)) ∧
    (∀ sigmaInf' DeltaE' : ℝ → ℝ, IntegrableOn (fun t => sigmaInf' t * DeltaE' t) (Set.Ioi 0) →
      ((∀ a : ℝ, (condDev (fun t => sigmaInf' t * DeltaE' t) a).re = (condDev (fun t => sigmaInf t * DeltaE t) a).re) →
        ∀ ω : ℝ, (condDev (fun t => sigmaInf' t * DeltaE' t) ω).im = (condDev (fun t => sigmaInf t * DeltaE t) ω).im) ∧
      ((∀ a : ℝ, (condDev (fun t => sigmaInf' t * DeltaE' t) a).im = (condDev (fun t => sigmaInf t * DeltaE t) a).im) →
        ∀ ω : ℝ, (condDev (fun t => sigmaInf' t * DeltaE' t) ω).re = (condDev (fun t => sigmaInf t * DeltaE t) ω).re)) := by sorry

end Arxiv1801_00461
