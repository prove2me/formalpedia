-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_validated_binding_orbits_transverse_hopf
-- name    : BirkhoffGlobalSection.validated_binding_orbits_transverse_hopf
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-05T01:07:04.603492+00:00
-- url     : https://prove2.me/theorems/dd13c45e-10ae-40f1-bbf0-cde155fd9927
-- title:
--   Validated retrograde and direct orbits of transverse Hopf type
-- statement:
--   Let $0<\mu\le 1/2$ and $2.1\le c\le 2.1+10^{-6}$, and let $\varphi$ be the Levi-Civita Hamiltonian flow on the selected component $\Sigma_{\mu,c}$. Then there are closed orbits $\gamma_r,\gamma_d$ of $\varphi$ such that:
--
--   - $\gamma_r$ satisfies the strict astronomical retrograde inequality of Joung--van Koert, Proposition 2.2, at every time, and $\gamma_d$ the strict direct inequality;
--   - for each of them, the radial projection $y\mapsto y/|y|$ of the orbit to the round sphere $S^3$ is the end of an antipodally equivariant transverse isotopy (for the standard contact structure $\ker(\tfrac12\sum q\,dp-p\,dq)$) that starts at the positive standard Hopf circle.
--
--   The second item says the orbits are transverse unknots of self-linking number $-1$, and that their antipodal images in $\mathbb{RP}^3$ are rational unknots, as for the symmetric orbits of the source.
--
--   This is the validated-numerics part of Joung--van Koert's Theorem 1.2. The two symmetric orbits are enclosed by computer-assisted shooting; the proof of Theorem 3.1 checks the sign conditions of Proposition 2.2 along them, and the simple, once-winding planar projection gives the Hopf knot type of the Levi-Civita lift.
-- source:
--   Joung--van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Theorem 1.2, Proposition 2.2, proof of Theorem 3.1.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

namespace BirkhoffGlobalSection

/-- Joung--van Koert, Theorem 1.2 with Proposition 2.2 and the proof of
Theorem 3.1: in the validated rectangle the Levi-Civita flow has a retrograde
and a direct closed orbit satisfying the strict astronomical sign conditions,
and the radial projection of each orbit to the round three-sphere is
equivariantly transversely isotopic to the positive standard Hopf circle
(unknotted, self-linking number `-1`). -/
theorem validated_binding_orbits_transverse_hopf (μ c : ℝ)
    (hμ0 : 0 < μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ γr γd : PeriodicOrbit φ,
      IsAstronomicallyRetrogradeOrbit φ γr ∧
      IsAstronomicallyDirectOrbit φ γd ∧
      Nonempty (EquivariantTransverseHopfIsotopy
        (radialNormalize '' orbitSet γr)) ∧
      Nonempty (EquivariantTransverseHopfIsotopy
        (radialNormalize '' orbitSet γd)) := by sorry

end BirkhoffGlobalSection
