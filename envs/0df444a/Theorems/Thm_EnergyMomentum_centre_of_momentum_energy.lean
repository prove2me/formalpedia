-- Prove2me | Theorems.Thm_EnergyMomentum_centre_of_momentum_energy
-- name    : EnergyMomentum.centre_of_momentum_energy
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:16:03.201286+00:00
-- url     : https://prove2.me/theorems/52bb26d8-e838-4f2d-91be-a6628028e9a1
-- title:
--   Centre-of-momentum frame: $\sum_n E_n = Mc^2$
-- statement:
--   Let $c>0$ and consider a finite system of particles indexed by a finite set $S$, with masses $m_n>0$ and velocities $|\mathbf v_n|<c$, energies $E_n$, momenta $\mathbf p_n$ and four-momenta $\mathbf P_n$ as above. If the system is observed in its centre-of-momentum frame, i.e.
--
--   $$
--   \sum_{n\in S}\mathbf p_n = \mathbf 0,
--   $$
--
--   then the total energy equals the invariant mass $M$ of the total four-momentum times $c^2$:
--
--   $$
--   \sum_{n\in S} E_n = Mc^2 .
--   $$
--
--   For instance, the internal kinetic energy of a gas in a container at rest is weighed as mass.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), §Many-particle systems → Centre-of-momentum frame.

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Centre-of-momentum frame: if `∑ 𝐩ₙ = 0` then `∑ Eₙ = M c²`. -/
theorem centre_of_momentum_energy {ι : Type} (s : Finset ι) (m : ι → ℝ) (v : ι → Vec3)
    (c : ℝ) (hc : 0 < c) (hm : ∀ n ∈ s, 0 < m n) (hv : ∀ n ∈ s, ‖v n‖ < c)
    (hcom : ∑ n ∈ s, momentum (m n) c (v n) = 0) :
    ∑ n ∈ s, energy (m n) c (v n)
      = invariantMass c (∑ n ∈ s, fourMomentum (m n) c (v n)) * c ^ 2 := by sorry

end EnergyMomentum
