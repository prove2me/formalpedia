-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_elliptic_rational_disk
-- name    : BirkhoffGlobalSection.geometric_retrograde_elliptic_rational_disk
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T04:54:52.946426+00:00
-- url     : https://prove2.me/theorems/7670d3bd-c7fc-4ff3-a292-b1119d60b4be
-- title:
--   A normalized geometric retrograde binding bounds a positive elliptic rational disk
-- statement:
--   Let $0<\mu<1$ and let the Jacobi value lie below the first critical value. Consider a convex conformally symplectic regularization model $M$ and a prime antipodal Levi-Civita trajectory whose physical projection is a collision-free simple geometric retrograde loop. Its doubled lift determines the normalized model binding
--
--   $$K=\operatorname{radialNormalize}\bigl(M(\operatorname{orbitSet}(\widetilde\delta))\bigr).$$
--
--   Then $K$ bounds a smooth embedded lifted rational two-disk with positive transverse boundary and exactly one positive elliptic characteristic singularity. In suitable disk parameters that singularity is at the origin and its characteristic vector field satisfies $DW(0)=\kappa\operatorname{id}$ for some $\kappa>0$. Antipodal points on the disk occur exactly at opposite boundary parameters.
--
--   This is a concrete spanning-disk statement. It does not assume or conclude an ambient contactomorphism, transverse isotopy, global surface of section, or return property.
--
--   **Formalization Note.** Establishing the rational-unknot class and self-linking in the specified arbitrary model contact structure remains part of the assertion. The geometric hypothesis allows angular reversals and does not impose immersion of the physical position projection. The single-singularity normal form is an additional characteristic-foliation simplification requirement, not a synonym for maximal self-linking.
-- source:
--   Geometric rational-unknot and self-linking identification: Hryniewicz–Salomão, arXiv:1505.02713v3, Section 1.3.1, https://arxiv.org/html/1505.02713v3; Hryniewicz–Salomão–Wysocki, arXiv:1912.01078v3, Section 1.3 and Definition 1.16. Disk simplification: Hryniewicz–Licata–Salomão, A dynamical characterization of universally tight lens spaces, arXiv:1306.6617, https://arxiv.org/pdf/1306.6617, Lemma 6.1 and the second paragraph of the proof of Proposition 6.4, pp. 36–38, using Lemma 3.10. Only the single-positive-elliptic disk construction is retained; the robust Reeb collar requiring the rotation hypothesis is not asserted. Positive primitive transport through arbitrary M, equivariant lifting, and parameter normalization are explicit adaptation obligations.

import Definitions.Def_BirkhoffGlobalSection_EllipticRationalDisk
open scoped ContDiff

namespace BirkhoffGlobalSection

theorem geometric_retrograde_elliptic_rational_disk
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ) :
    Nonempty (PositiveEllipticRationalDisk
      (radialNormalize '' (M.toModel ''
        orbitSet (antipodalTrajectoryDoubleLift φ hanti δ)))) := by sorry

end BirkhoffGlobalSection
