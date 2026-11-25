-- Prove2me | Theorems.Thm_Arxiv2105_07250_doppler_recorded_frequency
-- name    : Arxiv2105_07250.doppler_recorded_frequency
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T09:29:06.88446+00:00
-- url     : https://prove2.me/theorems/a3b8197d-051d-576c-a704-82c5406ad76a
-- title:
--   Eq. (5) (as proved): Doppler shift of the recorded frequency
-- statement:
--   Let $c>0$, $v\in\mathbb{R}^2$ with $0<|v|<c$, $\tilde\omega>0$ and $x\in\mathbb{R}^2$. For every $t'$ with $x\ne vt'$:
--
--   1. for every $\omega\in\mathbb{R}$, the phase $\mathrm{ph}_x(t')=(\omega+\tilde\omega)t'+\frac{\omega}{c}|x-vt'|-\frac\pi4$ of (A21) is stationary at $t'$ if and only if $\omega=-\breve\omega(x,t')$, where $\breve\omega(x,t')=\dfrac{\tilde\omega}{1-\frac{|v|}{c}\cos\theta_x(t')}$;
--   2. $\dfrac{\tilde\omega}{1+|v|/c}\le\breve\omega(x,t')\le\dfrac{\tilde\omega}{1-|v|/c}$;
--   3. $\breve\omega(x,t')>\tilde\omega$ if and only if the source is approaching $x$ ($\frac{d}{dt'}|x-vt'|<0$), $\breve\omega(x,t')<\tilde\omega$ if and only if it is receding ($\frac{d}{dt'}|x-vt'|>0$), and $\breve\omega(x,t')=\tilde\omega$ if and only if the source-receiver line is perpendicular to $S$ ($\cos\theta_x(t')=0$).
--
--   Finally $\breve\omega(x,t')\to\tilde\omega/(1-|v|/c)$ as $t'\to-\infty$ and $\breve\omega(x,t')\to\tilde\omega/(1+|v|/c)$ as $t'\to+\infty$.
--
--   **Formalization Note** The paper obtains (5) by setting the derivative (A22) of the phase (A21) to zero. With the paper's sign conventions the stationary frequency is $\omega=-\breve\omega$, so (5) is its magnitude; item 1 states what the computation gives. $\theta_x(t')$ is the angle between the vector from the source to $x$ and the direction of motion, which is the reading that (A22) uses. The consequences in the paper's text (a) are items 2-3 and the limits; the equal-frequency statement for collinear receivers is the separate statement `collinear_receivers_same_frequency`.
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), claim c028; Section 2, eq. (5), PDF p. 7; derivation in Appendix A.1, eqs. (A19)-(A23), PDF pp. 35-36

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv2105_07250

theorem doppler_recorded_frequency (c : ℝ) (hc : 0 < c) (v : Plane) (hv0 : v ≠ 0) (hv : ‖v‖ < c)
    (wt : ℝ) (hwt : 0 < wt) (x : Plane) :
    (∀ ω t' : ℝ, x ≠ t' • v →
      (deriv (dopplerPhase c ω wt x v) t' = 0 ↔ ω = -recordedFrequency c wt x v t')) ∧
    (∀ t' : ℝ, x ≠ t' • v →
      wt / (1 + ‖v‖ / c) ≤ recordedFrequency c wt x v t' ∧
        recordedFrequency c wt x v t' ≤ wt / (1 - ‖v‖ / c)) ∧
    (∀ t' : ℝ, x ≠ t' • v →
      (deriv (fun s : ℝ => ‖x - s • v‖) t' < 0 ↔ wt < recordedFrequency c wt x v t') ∧
      (0 < deriv (fun s : ℝ => ‖x - s • v‖) t' ↔ recordedFrequency c wt x v t' < wt) ∧
      (cosTheta x v t' = 0 ↔ recordedFrequency c wt x v t' = wt)) ∧
    Tendsto (recordedFrequency c wt x v) atBot (𝓝 (wt / (1 - ‖v‖ / c))) ∧
    Tendsto (recordedFrequency c wt x v) atTop (𝓝 (wt / (1 + ‖v‖ / c))) := by sorry

end Arxiv2105_07250
