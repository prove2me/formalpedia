-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_contact_hopf_equivalence
-- name    : BirkhoffGlobalSection.geometric_retrograde_contact_hopf_equivalence
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T04:38:40.835719+00:00
-- url     : https://prove2.me/theorems/33e02e71-4692-43f0-83d0-75d5e4186078
-- title:
--   Contact equivalence of a normalized geometric retrograde binding and the Hopf circle
-- statement:
--   Let $0<\mu<1$ and let the Jacobi value lie below the first critical value. Let $M$ be a convex conformally symplectic regularization model, and let $\delta$ be a prime antipodal periodic trajectory of the Levi-Civita Hamiltonian flow whose physical projection is a collision-free simple geometric retrograde loop. If $K$ is the radial normalization of the model image of its doubled lift, then there exists a coorientation-preserving contactomorphism of the standard sphere commuting with the antipodal involution such that
--
--   $$F(H(S^1))=K.$$
--
--   This identifies the binding up to a genuine ambient contactomorphism. It does not assert an isotopy, a spanning page, or any return property.
--
--   **Formalization Note.** The conclusion includes compatibility with the specified arbitrary convex regularization model, rather than assuming its coordinate map literally preserves the radial contact form. The geometric hypothesis permits angular reversals and states injectivity, but not nonvanishing derivative, of the physical position curve. Establishing the rational unknot class and rational self-linking $-1/2$ in these precise conventions, including any necessary treatment of projected turning points and the model contact primitive, remains part of this theorem.
-- source:
--   Geometric knot identification: Hryniewicz–Salomão, Elliptic bindings for dynamically convex Reeb flows on the real projective three-space, arXiv:1505.02713v3, Section 1.3.1, https://arxiv.org/html/1505.02713v3; Hryniewicz–Salomão–Wysocki, arXiv:1912.01078v3, Section 1.3 and Definition 1.16, https://arxiv.org/html/1912.01078v3. Classification up to contactomorphism: Baker–Etnyre, Rational Linking and contact geometry, corrected version, Theorem 5.1, pp. 10–13, https://etnyre.math.gatech.edu/preprints/papers/ratlink.pdf. This is an adapted regularization-coordinate formulation; positive contact-primitive compatibility and the equivariant lift are explicit additional obligations, not hypotheses silently added to the target.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open scoped ContDiff

namespace BirkhoffGlobalSection

theorem geometric_retrograde_contact_hopf_equivalence
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ) :
    ∃ F : EquivariantSphereContactomorphism,
      F.toFun '' (standardHopfCircle '' unitCircle) =
        radialNormalize '' (M.toModel ''
          orbitSet (antipodalTrajectoryDoubleLift φ hanti δ)) := by sorry

end BirkhoffGlobalSection
