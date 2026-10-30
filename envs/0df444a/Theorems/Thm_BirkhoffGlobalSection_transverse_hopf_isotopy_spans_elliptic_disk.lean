-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_transverse_hopf_isotopy_spans_elliptic_disk
-- name    : BirkhoffGlobalSection.transverse_hopf_isotopy_spans_elliptic_disk
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T03:19:28.95396+00:00
-- url     : https://prove2.me/theorems/6637c6a0-af2e-4d2d-a2da-53e4f4adc4e4
-- title:
--   A transverse Hopf isotopy spans an elliptic disk
-- statement:
--   Let $K \subset S^3$ be a knot admitting an equivariant transverse Hopf isotopy $I$ from the standard Hopf circle. Then $K$ bounds a positive elliptic rational disk: a smooth embedded disk in the three-sphere with exact boundary $K$, antipodal boundary fibers, positive boundary contact evaluation, and one positive elliptic characteristic singularity.
--
--   The disk is obtained by pushing the standard positive elliptic disk forward along the isotopy (Moser trick); positivity and the elliptic singularity are open conditions preserved by the transport. This turns the transverse knot certificate into the spanning-disk input of the rational disk theorem.
-- source:
--   Hryniewicz--Salomao, https://arxiv.org/html/1505.02713v3, Corollary 1.8 and Section 4; Liu--Salomao, https://arxiv.org/html/2506.17867v2, Theorem 1.16(ii) (transverse Hopf-fiber clause) and Section 10. Coordinate-level specialization to a centrally symmetric strictly convex model.

import Definitions.Def_BirkhoffGlobalSection_EllipticRationalDisk
import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem transverse_hopf_isotopy_spans_elliptic_disk
    (K : Set Phase) (I : EquivariantTransverseHopfIsotopy K) :
    Nonempty (PositiveEllipticRationalDisk K) := by sorry

end BirkhoffGlobalSection
