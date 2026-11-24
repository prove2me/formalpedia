-- Prove2me | Theorems.Thm_Arxiv1003_4724_static_permittivity_long_wave_limit
-- name    : Arxiv1003_4724.static_permittivity_long_wave_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:54:56.272572+00:00
-- url     : https://prove2.me/theorems/8e78231d-4d26-4cba-bf72-d0d8bb2da7d3
-- title:
--   Eq. (23): the static permittivity has the singularity $\kappa^2/q^2$, $\kappa^2=4\pi\langle Z^2\rangle/(TV)\ge0$
-- statement:
--   Let $\langle\cdot\rangle$ be a state on a complex $*$-algebra of observables. Let $N_a$ ($a$ in a finite set of species) be pairwise commuting self-adjoint number operators, let species $a$ carry charge $z_ae$ with $e>0$, and let $T>0$ and $V>0$. Assume quasi-neutrality $\sum_a e z_a n_a=0$ with $n_a=\langle N_a\rangle/V$ (eq. 3). Let $\varepsilon(q,0)$, $q>0$, be the static permittivity, and let $D_{ab}=(\partial n_a/\partial\mu_b)_{\mu_c,T}$. Assume the long-wavelength relation (eq. 18)
--
--   $$\lim_{q\to0}q^2\varepsilon(q,0)=4\pi\sum_{a,b}z_az_be^2D_{ab}$$
--
--   and the fluctuation identity $TD_{ab}=\langle\delta N_a\delta N_b\rangle/V$ (eq. 22). Then, with $Z=\sum_az_aeN_a$,
--
--   $$\lim_{q\to0}q^2\varepsilon(q,0)=\kappa^2=\frac{4\pi}{T}\frac{\langle Z^2\rangle}{V}\ge0 .$$
--
--   This is the $\kappa^2/q^2$ singularity of the static permittivity at long wavelengths.
--
--   **Formalization Note** Eqs. (18) and (22), which the paper quotes from refs. [6-9], are hypotheses. $D_{ab}$ is a given real matrix tied to the fluctuations by (22). The limit is one-sided ($q\to0^+$, $q$ the modulus of the wave vector). The conclusion states $\kappa^2$ as a complex number that is real ($\operatorname{Im}=0$) and nonnegative. All quantities are taken at the fixed volume $V$ in which the paper writes eq. (23).
-- source:
--   Bobrov, Trigger, van Heijst and Schram, Kramers-Kronig relations for the dielectric function and the static conductivity of Coulomb systems, arXiv:1003.4724v1 (2010), claim c015; Sec. II, eq. (23) from eqs. (18), (22) and (3), PDF p. 5; restated in Sec. IV, PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology

namespace Arxiv1003_4724

theorem static_permittivity_long_wave_limit {A ι : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Fintype ι]
    (ω : A →ₗ[ℂ] ℂ) (hω : IsState ω) (N : ι → A) (hN : ∀ a, IsSelfAdjoint (N a))
    (hNc : ∀ a b, Commute (N a) (N b)) (z : ι → ℝ) (e T V : ℝ) (he : 0 < e) (hT : 0 < T)
    (hV : 0 < V) (h3 : IsQuasiNeutral ω N z e V) (epsStatic : ℝ → ℝ) (D : ι → ι → ℝ)
    (h18 : Tendsto (fun q => q ^ 2 * epsStatic q) (𝓝[>] (0 : ℝ))
      (𝓝 (4 * Real.pi * ∑ a, ∑ b, z a * z b * e ^ 2 * D a b)))
    (h22 : ∀ a b, ((T * D a b : ℝ) : ℂ) = numberCov ω N a b / V) :
    Tendsto (fun q => ((q ^ 2 * epsStatic q : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
        (𝓝 (kappaSq ω N z e T V)) ∧
      (kappaSq ω N z e T V).im = 0 ∧ 0 ≤ (kappaSq ω N z e T V).re := by sorry

end Arxiv1003_4724
