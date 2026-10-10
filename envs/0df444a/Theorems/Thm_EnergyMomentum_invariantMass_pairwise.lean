-- Prove2me | Theorems.Thm_EnergyMomentum_invariantMass_pairwise
-- name    : EnergyMomentum.invariantMass_pairwise
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:16:39.447562+00:00
-- url     : https://prove2.me/theorems/841918ba-8fed-428a-a837-c7ca3ecaa435
-- title:
--   Total mass versus individual masses
-- statement:
--   Let $c>0$ and consider $N$ particles $n = 0,\dots,N-1$ with masses $m_n>0$ and velocities $|\mathbf v_n|<c$, energies $E_n$, momenta $\mathbf p_n$, and let $M$ be the invariant mass of the total four-momentum $\sum_n\mathbf P_n$. Then
--
--   $$
--   \left(Mc^2\right)^2 - \sum_{n}\left(m_nc^2\right)^2 = 2\sum_{n<k}\left(E_nE_k - c^2\,\mathbf p_n\cdot\mathbf p_k\right).
--   $$
--
--   Since $M$ and the $m_n$ are invariants, the right-hand side is invariant too, although each $E_n$ and $\mathbf p_n$ is measured in a particular frame.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), §Many-particle systems → Relating total mass to individual masses (display after substituting the individual masses $m_n$ into (2), and its rearranged form).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Total mass versus individual masses:
`(M c²)² − ∑ₙ (mₙ c²)² = 2 ∑_{n<k} (Eₙ E_k − c² 𝐩ₙ · 𝐩_k)`. -/
theorem invariantMass_pairwise (N : ℕ) (m : Fin N → ℝ) (v : Fin N → Vec3)
    (c : ℝ) (hc : 0 < c) (hm : ∀ n, 0 < m n) (hv : ∀ n, ‖v n‖ < c) :
    (invariantMass c (∑ n, fourMomentum (m n) c (v n)) * c ^ 2) ^ 2
        - ∑ n, (m n * c ^ 2) ^ 2
      = 2 * ∑ n, ∑ k ∈ Finset.Ioi n,
          (energy (m n) c (v n) * energy (m k) c (v k)
            - c ^ 2 * inner ℝ (momentum (m n) c (v n)) (momentum (m k) c (v k))) := by sorry

end EnergyMomentum
