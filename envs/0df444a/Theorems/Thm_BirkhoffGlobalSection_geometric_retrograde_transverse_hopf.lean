-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_transverse_hopf
-- name    : BirkhoffGlobalSection.geometric_retrograde_transverse_hopf
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T02:10:24.242997+00:00
-- url     : https://prove2.me/theorems/cb7fa7c4-b954-448a-985b-ad58d11273a6
-- title:
--   Geometric retrograde binding has equivariant transverse Hopf type
-- statement:
--   Assume $0<\mu<1$ and $-c<h_1(\mu)$. Let $M$ be a convex regularization model, $\varphi$ a complete antipodally equivariant LC Hamiltonian flow, and $\delta$ a geometric Birkhoff retrograde trajectory. Write $\widetilde\delta$ for its closed double lift and $F$ for the regularization map.
--
--   The normalized model binding admits an actual equivariant transverse Hopf isotopy:
--
--   $$
--   \operatorname{Nonempty}\left(\operatorname{EquivariantTransverseHopfIsotopy}
--    \left(N\bigl(F(\widetilde\delta)\bigr)\right)\right).
--   $$
--
--   The isotopy consists of smooth embedded circles on the round sphere, commutes with antipodes, starts at the positive standard Hopf circle, and remains positively transverse to the radial contact structure throughout.
--
--   This is an additional geometric identification obligation for the decomposition, containing no page or return assertion. It includes compatibility of the physical and model contact structures, orientation conventions, and an equivariant lift of the isotopy. Conformal symplecticity of the coordinate change alone is not asserted to preserve the radial primitive literally.
--
--   The source identifies the geometric retrograde orbit as a rational unknot with self-linking $-1/2$. The stronger explicit isotopy formulation here needs its own geometric construction or an appropriate transverse-classification argument; equality of self-linking numbers or existence of a contactomorphism is not silently substituted for that isotopy.
-- source:
--   Hryniewicz--Salomao, https://arxiv.org/html/1505.02713v3, Section 1.3.1 identifies the geometric Birkhoff orbit as a 2-unknot of rational self-linking -1/2. Liu--Salomao, https://arxiv.org/html/2506.17867v2, Theorem 1.16(ii) includes the transverse Hopf-fiber criterion. This explicit equivariant-isotopy identification is a new auxiliary obligation for the decomposition and is stronger than the statement explicitly made in Section 1.3.1; it is not claimed to follow merely from the numerical self-linking value.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

namespace BirkhoffGlobalSection

/-- Identify the normalized geometric retrograde binding with the positive
Hopf transverse isotopy class, through equivariant embeddings. This includes
compatibility of the physical and model contact structures. -/
theorem geometric_retrograde_transverse_hopf
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ) :
    Nonempty (EquivariantTransverseHopfIsotopy
      (radialNormalize '' (M.toModel ''
        orbitSet (antipodalTrajectoryDoubleLift φ hanti δ)))) := by sorry

end BirkhoffGlobalSection
