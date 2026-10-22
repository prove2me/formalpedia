-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_disk_like_global_section_of_transverse_hopf
-- name    : BirkhoffGlobalSection.disk_like_global_section_of_transverse_hopf
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-05T01:07:16.822954+00:00
-- url     : https://prove2.me/theorems/2206e58a-f2fd-40d0-aa35-01fe2edfb672
-- title:
--   Hryniewicz binding criterion on the Levi-Civita component
-- statement:
--   Let $0<\mu<1$ and let $c$ be below the first critical value. Assume the selected Levi-Civita component $\Sigma_{\mu,c}$ is strictly star-shaped, $dK(s)\,s>0$ on $\Sigma_{\mu,c}$, and that its Hamiltonian flow is dynamically convex: every closed orbit has Conley--Zehnder index at least $3$, in the winding form `IsDynamicallyConvexOn`. Let $\varphi$ be the Hamiltonian flow on $\Sigma_{\mu,c}$ and $\gamma$ a closed orbit whose radial projection to $S^3$ is equivariantly transversely isotopic to the positive Hopf circle. Then $\gamma$ bounds a disk-like global surface of section: a smooth embedded disk $D\subset\Sigma_{\mu,c}$ with $\partial D=\gamma$ and interior transverse to the flow, which every other trajectory meets in arbitrarily large positive and negative time.
--
--   Since $\Sigma_{\mu,c}$ is compact and strictly star-shaped, radial projection identifies it with $(S^3,\xi_{\mathrm{std}})$, and the flow is a reparametrized Reeb flow. Hryniewicz's theorem then applies: for a dynamically convex Reeb flow on the tight three-sphere, a periodic orbit bounds a disk-like global section if and only if it is unknotted with self-linking number $-1$, which is the transverse Hopf type.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. (2014), https://arxiv.org/abs/1105.2077 (characterization of the binding orbits of disk-like global sections, without genericity assumptions); Hofer--Wysocki--Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998); used as in Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Theorem 1.5.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

namespace BirkhoffGlobalSection

/-- Hryniewicz's binding criterion on the Levi-Civita component. Below the
first critical value, if the selected component is strictly star-shaped and its
Hamiltonian flow is dynamically convex, then every closed orbit whose radial
projection is transversely isotopic to the positive Hopf circle bounds a
disk-like global surface of section. -/
theorem disk_like_global_section_of_transverse_hopf (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (hstar : ∀ s ∈ leftEnergyComponent μ c,
      0 < fderiv ℝ (leviCivitaHamiltonian μ c) s s)
    (hdc : IsDynamicallyConvexOn (leviCivitaHamiltonian μ c)
      (leftEnergyComponent μ c))
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (γ : PeriodicOrbit φ)
    (hhopf : Nonempty (EquivariantTransverseHopfIsotopy
      (radialNormalize '' orbitSet γ))) :
    DiskLikeGlobalSurfaceOfSection φ γ := by sorry

end BirkhoffGlobalSection
