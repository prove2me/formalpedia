-- Prove2me | Theorems.Thm_EnergyMomentum_system_energy_momentum_relation
-- name    : EnergyMomentum.system_energy_momentum_relation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:15:34.863788+00:00
-- url     : https://prove2.me/theorems/ae86df67-d92f-4466-90f7-7c4663b0df03
-- title:
--   Many-particle energy–momentum relation (2)
-- statement:
--   Let $c>0$ and consider a finite system of particles indexed by a finite set $S$, particle $n$ having mass $m_n>0$ and velocity $\mathbf v_n$ with $|\mathbf v_n|<c$, energy $E_n = \gamma_n m_n c^2$, momentum $\mathbf p_n = \gamma_n m_n\mathbf v_n$ and four-momentum $\mathbf P_n = (E_n/c, \mathbf p_n)$. Let $M$ be the invariant mass of the total four-momentum, $M = \sqrt{\langle \sum_n\mathbf P_n, \sum_n\mathbf P_n\rangle}/c$. Then
--
--   $$
--   \left(\sum_{n\in S} E_n\right)^2 = \left(\Big|\sum_{n\in S}\mathbf p_n\Big|\, c\right)^2 + \left(Mc^2\right)^2 .
--   $$
--
--   The energies and momenta are frame-dependent while $M$ is not; $M$ is in general different from $\sum_n m_n$.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), §Many-particle systems → Addition of four-momenta, equation (2).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Many-particle energy–momentum relation (2):
`(∑ Eₙ)² = (|∑ 𝐩ₙ| c)² + (M c²)²`, where `M` is the invariant mass of the total four-momentum. -/
theorem system_energy_momentum_relation {ι : Type} (s : Finset ι) (m : ι → ℝ) (v : ι → Vec3)
    (c : ℝ) (hc : 0 < c) (hm : ∀ n ∈ s, 0 < m n) (hv : ∀ n ∈ s, ‖v n‖ < c) :
    (∑ n ∈ s, energy (m n) c (v n)) ^ 2
      = (‖∑ n ∈ s, momentum (m n) c (v n)‖ * c) ^ 2
        + (invariantMass c (∑ n ∈ s, fourMomentum (m n) c (v n)) * c ^ 2) ^ 2 := by sorry

end EnergyMomentum
