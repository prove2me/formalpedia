-- Prove2me | Theorems.Thm_DarkEnergyLCDM_luminosity_distance_flat_limit
-- name    : DarkEnergyLCDM.luminosity_distance_flat_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T01:06:31.29503+00:00
-- url     : https://prove2.me/theorems/e236d8e8-28d8-4e6d-8b2c-38b7e23bb7ab
-- title:
--   Luminosity distance: curved branches tend to the flat one as $\Omega_k\to0$
-- statement:
--   Let $H$ be any real function of redshift, $H_0\neq0$ and $z\in\mathbb R$. Let $d_L(\Omega_k)$ be the luminosity distance of the definition file, with $\sinh$ for $\Omega_k>0$, the flat formula for $\Omega_k=0$ and $\sin$ for $\Omega_k<0$, all built from the comoving distance $\chi(z)=\int_0^z d\tilde z/H(\tilde z)$. Then
--   $$\lim_{\Omega_k\to0,\ \Omega_k\neq0} d_L(\Omega_k) = d_L(0) = (1+z)\,\chi(z).$$
--
--   The three-branch expression for $d_L$ below Eq. (11) therefore defines a single quantity that is continuous across the flat case.
--
--   **Formalization Note** The source prints the prefactor $1/(1+z)$ and puts $\sin$ in the $\Omega_k>0$ branch. With its own convention $\Omega_k=-K/H_0^2$, the standard luminosity distance has $(1+z)$ and $\sinh$ for $\Omega_k>0$, and that standard form is used here. The limit statement holds for either convention.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 66, Eq. (11) and the luminosity-distance formula

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

open Filter Topology

theorem luminosity_distance_flat_limit (H : ℝ → ℝ) (H₀ : ℝ) (hH₀ : H₀ ≠ 0) (z : ℝ) :
    Tendsto (fun Ωk : ℝ => luminosityDistance H H₀ Ωk z) (𝓝[≠] 0)
      (𝓝 (luminosityDistance H H₀ 0 z)) := by sorry

end DarkEnergyLCDM
