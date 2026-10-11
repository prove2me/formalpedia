-- Prove2me | Theorems.Thm_DarkEnergyLCDM_hubble_evolution
-- name    : DarkEnergyLCDM.hubble_evolution
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T00:59:06.745651+00:00
-- url     : https://prove2.me/theorems/715a1b71-5fa8-4fcc-9526-e03e8de6d08b
-- title:
--   ΛCDM expansion history $H^2 = H_0^2(\Omega_r a^{-4}+\Omega_m a^{-3}+\Omega_k a^{-2}+\Omega_\Lambda)$
-- statement:
--   Let $(a, \rho_r, \rho_m)$ be a ΛCDM background on an open connected time interval $I$, with constants $G$, $K$, $\Lambda$. This means that $a$ is $C^2$ and positive, the Friedmann equation (2) holds for $\rho = \rho_r + \rho_m$, and radiation ($p_r=\rho_r/3$) and matter ($p_m=0$) each satisfy the continuity equation (3). Let $t_0\in I$ with $a(t_0)=1$, and suppose $H_0 = H(t_0) \neq 0$. Then for every $t \in I$,
--   $$H(t)^2 = H_0^2\left(\Omega_r\,a(t)^{-4} + \Omega_m\,a(t)^{-3} + \Omega_k\,a(t)^{-2} + \Omega_\Lambda\right),$$
--   where $\Omega_r = \frac{8\pi G}{3H_0^2}\rho_r(t_0)$, $\Omega_m = \frac{8\pi G}{3H_0^2}\rho_m(t_0)$, $\Omega_k = -K/H_0^2$ and $\Omega_\Lambda = \Lambda/(3H_0^2)$.
--
--   This is Eq. (5) of the source, the expansion history of the standard model that is used in every fit of cosmological distances.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 65, Eq. (5) (with Eqs. (2)–(4), (6))

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

open Real

theorem hubble_evolution (G K Λ : ℝ) (I : Set ℝ) (a ρr ρm : ℝ → ℝ)
    (hbg : IsLCDMBackground G K Λ I a ρr ρm) (t₀ : ℝ) (ht₀ : t₀ ∈ I) (ha₀ : a t₀ = 1)
    (hH₀ : hubble a t₀ ≠ 0) :
    ∀ t ∈ I, hubble a t ^ 2 = hubble a t₀ ^ 2 *
      (densityParam G (hubble a t₀) (ρr t₀) * (a t)⁻¹ ^ 4
        + densityParam G (hubble a t₀) (ρm t₀) * (a t)⁻¹ ^ 3
        + curvatureParam K (hubble a t₀) * (a t)⁻¹ ^ 2
        + lambdaParam Λ (hubble a t₀)) := by sorry

end DarkEnergyLCDM
