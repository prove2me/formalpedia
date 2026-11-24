-- Prove2me | Theorems.Thm_Arxiv1510_02920_exiting_wave_reflectionless
-- name    : Arxiv1510_02920.exiting_wave_reflectionless
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:14:08.182595+00:00
-- url     : https://prove2.me/theorems/22f6a01c-c6e1-4849-bdd4-bea70f05177a
-- title:
--   Eqs. (2)-(4), (8) and Fig. 1: a passive planar permittivity that does not reflect perpendicularly exiting waves of any frequency
-- statement:
--   Let $c>0$, $a>0$, $\Omega\ne0$. For $\gamma>0$ let
--
--   $$\varepsilon_\gamma(x,\omega)=P(x,\omega)^2-\frac{ic}{\omega}\partial_xP(x,\omega),\qquad P(x,\omega)=1+\frac{f(x)}{(\gamma-i\omega)^2},\qquad f(x)=\frac{\Omega^2}{2}\big[1+\tanh(-x/a)\big],$$
--
--   and $n_-(\omega)=1+\Omega^2/(\gamma-i\omega)^2$, $k_0=\omega/c$.
--
--   1. For every $\gamma>0$:
--      - for every real $\omega\ne0$, $\varepsilon_\gamma(x,\omega)\to1$ and $P(x,\omega)\to1$ as $x\to+\infty$ (vacuum), and $\varepsilon_\gamma(x,\omega)\to n_-(\omega)^2$ and $P(x,\omega)\to n_-(\omega)$ as $x\to-\infty$ (a homogeneous dispersive material);
--      - $\varepsilon_\gamma$ satisfies conditions (i), (ii), (iv) and (v);
--      - for every real $\omega\ne0$ and $E_0\ne0$, the wave $E(x)=E_0\exp[ik_0\int_0^xP]$ solves the Helmholtz equation $E''+k_0^2\varepsilon_\gamma E=0$ at every $x$, it is everywhere the local right-going mode, $E'(x)=ik_0P(x,\omega)E(x)$ for all $x$, and there are $T,A\ne0$ with
--
--   $$E(x)e^{-ik_0x}\to T\ (x\to+\infty),\qquad E(x)e^{-ik_0n_-(\omega)x}\to A\ (x\to-\infty).$$
--   2. For all sufficiently large $\gamma$, $\varepsilon_\gamma$ also satisfies condition (iii) (no gain).
--
--   Thus for $\gamma$ not too small the material is passive and obeys the Kramers–Kronig relations. At every frequency a perpendicular wave passes from the material on the left into the vacuum on the right as a single right-going wave, with no reflection.
--
--   **Formalization Note** Absence of reflection is expressed through the first-order equation $E'=ik_0PE$ at every $x$, with $P\to n_-$ on the left and $P\to1$ on the right: the field is everywhere the local right-going mode and has no counter-propagating part. The plane-wave limits alone would not show this on the absorbing left side, where a left-going component $e^{-ik_0n_-x}$ decays as $x\to-\infty$ and is invisible to the limit; only the limit in the vacuum on the right excludes a reflected wave by itself. "$\gamma$ not too small" is read as "for all sufficiently large $\gamma$" and is needed only for condition (iii). The hypothesis $\Omega\ne0$ is implicit in the paper.
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c018; abstract and unnumbered main text, eqs. (2), (3), (4), (8), paragraph after Figure 1, PDF pp. 1, 3-5

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem exiting_wave_reflectionless (c a Om : ℝ) (hc : 0 < c) (ha : 0 < a) (hOm : Om ≠ 0) :
    (∀ γ : ℝ, 0 < γ →
      (∀ ω : ℝ, ω ≠ 0 →
        Tendsto (fun x : ℝ => tanhPerm c Om a γ x (ω : ℂ)) atTop (𝓝 1) ∧
        Tendsto (fun x : ℝ => tanhPerm c Om a γ x (ω : ℂ)) atBot
          (𝓝 (mediumIndex Om γ ω ^ 2)) ∧
        Tendsto (fun x : ℝ => tanhP Om a γ x (ω : ℂ)) atTop (𝓝 1) ∧
        Tendsto (fun x : ℝ => tanhP Om a γ x (ω : ℂ)) atBot (𝓝 (mediumIndex Om γ ω))) ∧
      CondAnalytic (tanhPerm c Om a γ) ∧ CondReality (tanhPerm c Om a γ) ∧
      CondLowFreq (-1) (tanhPerm c Om a γ) ∧ CondHighFreq (tanhPerm c Om a γ) ∧
      (∀ ω : ℝ, ω ≠ 0 → ∀ E0 : ℂ, E0 ≠ 0 →
        (∀ x, HelmholtzAt c ω (fun y => tanhPerm c Om a γ y (ω : ℂ))
          (waveField c E0 (tanhP Om a γ) ω) x) ∧
        (∀ x, deriv (waveField c E0 (tanhP Om a γ) ω) x =
          Complex.I * ((ω / c : ℝ) : ℂ) * tanhP Om a γ x (ω : ℂ) *
            waveField c E0 (tanhP Om a γ) ω x) ∧
        (∃ T : ℂ, T ≠ 0 ∧ Tendsto (fun x : ℝ => waveField c E0 (tanhP Om a γ) ω x *
          Complex.exp (-(Complex.I * ((ω / c : ℝ) : ℂ) * x))) atTop (𝓝 T)) ∧
        (∃ A : ℂ, A ≠ 0 ∧ Tendsto (fun x : ℝ => waveField c E0 (tanhP Om a γ) ω x *
          Complex.exp (-(Complex.I * ((ω / c : ℝ) : ℂ) * mediumIndex Om γ ω * x))) atBot
          (𝓝 A)))) ∧
    ∀ᶠ γ in atTop, CondNoGain (tanhPerm c Om a γ) := by sorry

end Arxiv1510_02920
