-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_elliptic_rational_disks_contact_equivalent
-- name    : BirkhoffGlobalSection.positive_elliptic_rational_disks_contact_equivalent
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T04:54:50.362316+00:00
-- url     : https://prove2.me/theorems/95cf5795-1051-47ed-8e05-cbcd21d66b8a
-- title:
--   Positive elliptic rational disks have contact-equivalent boundaries
-- statement:
--   Let $K,L\subset S^3$ each bound a smooth embedded lifted rational two-disk, with opposite boundary parameters giving exactly the antipodal coincidences. Assume both boundaries are positively transverse to the standard contact form, and each disk has precisely one positive elliptic characteristic singularity in the specified scalar linear normal form. Then an antipodally equivariant, coorientation-preserving contactomorphism of the standard sphere carries one boundary to the other:
--
--   $$F(K)=L.$$
--
--   The disk hypotheses determine the rational unknot class and rational self-linking $-1/2$ in the antipodal quotient. This is the two-fold-cover formulation of weak transverse simplicity for these rational unknots in the standard tight contact structure on $\mathbb{RP}^3$. It is independent of any Hamiltonian flow or regularization model.
--
--   **Formalization Note.** The conclusion includes a smooth inverse and the positive contact pullback equation on sphere-tangent vectors; no contact isotopy is asserted.
-- source:
--   Baker–Etnyre, Rational Linking and contact geometry, corrected version, https://etnyre.math.gatech.edu/preprints/papers/ratlink.pdf, Lemma 1.1 (characteristic-foliation formula for rational self-linking, p. 4), Theorem 5.1 and its proof (weak transverse simplicity, pp. 10–13), specialized to p=2. A single positive elliptic singularity gives rational self-linking -1/2; Section 5.1 and the p=2 case of the proof identify the oriented rational-unknot types. Lift the quotient contactomorphism through S^3 to obtain the stated odd map.

import Definitions.Def_BirkhoffGlobalSection_EllipticRationalDisk
open scoped ContDiff

namespace BirkhoffGlobalSection

theorem positive_elliptic_rational_disks_contact_equivalent
    (K L : Set Phase)
    (DK : PositiveEllipticRationalDisk K)
    (DL : PositiveEllipticRationalDisk L) :
    ∃ F : EquivariantSphereContactomorphism, F.toFun '' K = L := by sorry

end BirkhoffGlobalSection
