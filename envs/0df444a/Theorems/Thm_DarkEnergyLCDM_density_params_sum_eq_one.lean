-- Prove2me | Theorems.Thm_DarkEnergyLCDM_density_params_sum_eq_one
-- name    : DarkEnergyLCDM.density_params_sum_eq_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T01:02:46.548147+00:00
-- url     : https://prove2.me/theorems/779bd98e-42ec-4cd2-af95-5ba03a036492
-- title:
--   Density parameters sum to one: $\Omega_\Lambda+\Omega_m+\Omega_r+\Omega_k=1$
-- statement:
--   Let $(a, \rho_r, \rho_m)$ be a ΛCDM background on $I$ with constants $G, K, \Lambda$. Let $t_0\in I$ with $a(t_0)=1$ and $H_0 = H(t_0)\neq 0$. With the density parameters of Eq. (6) evaluated at $t_0$,
--   $$\Omega_\Lambda + \Omega_m + \Omega_r + \Omega_k = 1.$$
--
--   This is the closure condition stated after Eq. (6).
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 65, after Eq. (6)

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

theorem density_params_sum_eq_one (G K Λ : ℝ) (I : Set ℝ) (a ρr ρm : ℝ → ℝ)
    (hbg : IsLCDMBackground G K Λ I a ρr ρm) (t₀ : ℝ) (ht₀ : t₀ ∈ I) (ha₀ : a t₀ = 1)
    (hH₀ : hubble a t₀ ≠ 0) :
    lambdaParam Λ (hubble a t₀) + densityParam G (hubble a t₀) (ρm t₀)
      + densityParam G (hubble a t₀) (ρr t₀) + curvatureParam K (hubble a t₀) = 1 := by sorry

end DarkEnergyLCDM
