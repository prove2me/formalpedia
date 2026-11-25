-- Prove2me | Theorems.Thm_Arxiv1003_4724_long_wave_permittivity_kubo_form
-- name    : Arxiv1003_4724.long_wave_permittivity_kubo_form
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T23:56:12.309886+00:00
-- url     : https://prove2.me/theorems/539798b8-48f9-487e-b4e3-b22e6a723489
-- title:
--   Eqs. (24)-(26): the long-wavelength permittivity in conductivity form with the Kubo conductivity
-- statement:
--   Let $\langle\cdot\rangle$ and $X\mapsto X(t)$ form a long-wavelength model with self-adjoint dipole components $P^\beta$ and current components $I^\beta$ satisfying $dP^\beta/dt=I^\beta$ (eq. 26). Let $\hbar,V,e>0$, let $N_a$ be self-adjoint number operators, and let $z_a$ and $m_a>0$ be the charge numbers and masses. Write $\omega_p^2=\sum_a4\pi z_a^2e^2n_a/m_a$ (eq. 21), and assume the sum rule $\frac{4\pi i}{3\hbar V}\langle[I^\beta,P^\beta]\rangle=\omega_p^2$ (eq. 26). With $\varphi(z)=\frac{4\pi}{3V}\langle\!\langle I^\beta|I^\beta\rangle\!\rangle_z$ (eq. 20) and the Kubo conductivity $\sigma(z)=-\frac1{3V}\langle\!\langle I^\beta|P^\beta\rangle\!\rangle_z$ (eq. 25):
--
--   1. For every $z$ with $\operatorname{Im}z>0$,
--   $$1-\frac{\omega_p^2}{z^2}-\frac{\varphi(z)}{z^2}=1+\frac{4\pi i\,\sigma(z)}{z}.$$
--   2. Let $x\ne0$ be real, and let $\varepsilon(q,x)$ and $\sigma(q,x)$ ($q>0$) satisfy $\varepsilon(q,x)=1+4\pi i\sigma(q,x)/x$ (eq. 13). Suppose $\varepsilon(q,x)\to E$ as $q\to0$, and suppose $E$ is the boundary value at $x+i0$ of the right-hand side of (19), $1-\omega_p^2/z^2-\varphi(z)/z^2$ (eq. 19). Suppose further that $\sigma(x+i\eta)\to s$ as $\eta\to0^+$. Then
--   $$E=1+\frac{4\pi i\,s}{x},\qquad s=\lim_{q\to0}\sigma(q,x)\quad\text{(eq. 24)}.$$
--
--   So the long-wavelength permittivity (19) has the conductivity form (24), and its conductivity is given by the Kubo formula.
--
--   **Formalization Note** Eqs. (13) and (19) are premises quoted by the paper and enter part 2 as hypotheses. The boundary values $\omega+i0$ are written as limits $\eta\to0^+$, and the existence of the boundary value of the Kubo conductivity is assumed. The integration by parts behind part 1 uses stationarity of the state and the boundedness and continuity of the correlation functions, which are part of the long-wavelength model.
-- source:
--   Bobrov, Trigger, van Heijst and Schram, Kramers-Kronig relations for the dielectric function and the static conductivity of Coulomb systems, arXiv:1003.4724v1 (2010), claim c004; Sec. II, eqs. (24)-(26) from eqs. (19)-(21) and (13), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology

namespace Arxiv1003_4724

theorem long_wave_permittivity_kubo_form {A ι : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Fintype ι]
    (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Fin 3 → A)
    (hM : IsLongWaveModel ω τ Dip Cur) (hbar V e : ℝ) (hhbar : 0 < hbar) (hV : 0 < V)
    (he : 0 < e) (N : ι → A) (hN : ∀ a, IsSelfAdjoint (N a)) (z m : ι → ℝ)
    (hm : ∀ a, 0 < m a)
    (h26 : 4 * Real.pi * Complex.I / (3 * hbar * V) * ∑ β, ω ⁅Cur β, Dip β⁆ =
      (plasmaFreqSq z e (meanDensity ω N V) m : ℂ)) :
    (∀ w : ℂ, 0 < w.im →
      1 - (plasmaFreqSq z e (meanDensity ω N V) m : ℂ) / w ^ 2 - phiFn ω τ hbar V Cur w / w ^ 2 =
        1 + 4 * Real.pi * Complex.I * kuboSigma ω τ hbar V Dip Cur w / w) ∧
    (∀ (epsQ sigQ : ℝ → ℝ → ℂ) (x : ℝ), x ≠ 0 → ∀ E s : ℂ,
      (∀ q : ℝ, 0 < q → epsQ q x = 1 + 4 * Real.pi * Complex.I * sigQ q x / x) →
      Tendsto (fun q => epsQ q x) (𝓝[>] (0 : ℝ)) (𝓝 E) →
      Tendsto (fun η : ℝ => 1 - (plasmaFreqSq z e (meanDensity ω N V) m : ℂ) /
          ((x : ℂ) + η * Complex.I) ^ 2 -
          phiFn ω τ hbar V Cur ((x : ℂ) + η * Complex.I) / ((x : ℂ) + η * Complex.I) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 E) →
      Tendsto (fun η : ℝ => kuboSigma ω τ hbar V Dip Cur ((x : ℂ) + η * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 s) →
      E = 1 + 4 * Real.pi * Complex.I * s / x ∧
        Tendsto (fun q => sigQ q x) (𝓝[>] (0 : ℝ)) (𝓝 s)) := by sorry

end Arxiv1003_4724
