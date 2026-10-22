-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_leviCivita_regularAt_collisionFree_subcritical_energy
-- name    : BirkhoffGlobalSection.leviCivita_regularAt_collisionFree_subcritical_energy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:18:53.627908+00:00
-- url     : https://prove2.me/theorems/5d0d4018-50af-4964-8041-4d7998b2156f
-- title:
--   Regularity of collision-free subcritical Levi-Civita states
-- statement:
--   Let $0<\mu<1$ and $-c$ lie below the first critical value of the Jacobi Hamiltonian. Suppose the Levi-Civita state $s=(z,w)$ has $z\ne0$, stays away from the second collision, and lies on $K_{\mu,c}=0$. Then
--
--   $$
--   dK_{\mu,c}(s)\ne0.
--   $$
--
--   On this collision-free domain, the Levi-Civita transformation is locally invertible and Equation (2.2) identifies $K$ with the positive position factor times $H_\mu+c$. A zero derivative of $K$ on its zero level would therefore give a Jacobi critical point of value $-c$, contradicting the strict subcritical hypothesis. This statement holds on every collision-free component of that energy level.
-- source:
--   Joung--van Koert, Equation (2.2) and Proposition 2.4, https://arxiv.org/abs/2407.19159v3, PDF pp. 6–7. The collision calculation uses the displayed Levi-Civita Hamiltonian; the collision-free case uses its local coordinate relation to the Jacobi Hamiltonian below the first critical value.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Away from both collisions the Levi-Civita coordinate map is locally
invertible; a critical point at subcritical energy would give a Jacobi
critical value below the first one. -/
theorem leviCivita_regularAt_collisionFree_subcritical_energy (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (s : Phase)
    (hK : leviCivitaHamiltonian μ c s = 0)
    (hD : 0 < secondCollisionDistanceSq s)
    (hz : 0 < zNormSq s) :
    fderiv ℝ (leviCivitaHamiltonian μ c) s ≠ 0 := by sorry

end BirkhoffGlobalSection
