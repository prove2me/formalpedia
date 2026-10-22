-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_leviCivita_transverse_hopf
-- name    : BirkhoffGlobalSection.geometric_retrograde_leviCivita_transverse_hopf
-- status  : Open
-- author  : @caleb
-- created : 2026-10-01T01:06:45.117313+00:00
-- url     : https://prove2.me/theorems/d1a3bf91-534f-4f64-854c-a68b311c8380
-- title:
--   The Levi-Civita retrograde binding is a transverse Hopf fiber
-- statement:
--   Let $0<\mu<1$ and let the Jacobi value lie below the first critical value. Let $\varphi$ be the Levi-Civita Hamiltonian flow on the selected left energy component, antipodally equivariant. Let $\delta$ be a prime antipodal periodic trajectory whose physical projection is a collision-free simple loop with winding number one around the primary and the $q_2$-reflection symmetry (a geometric Birkhoff retrograde trajectory). Write $\widetilde\delta$ for its closed double lift and $N(y) = y/|y|$ for radial normalization onto the round sphere $S^3$. Then
--
--   $$
--   \operatorname{Nonempty}\Bigl(\operatorname{EquivariantTransverseHopfIsotopy}\bigl(N(\widetilde\delta)\bigr)\Bigr).
--   $$
--
--   That is, there is a smooth isotopy of embedded circles on $S^3$ with the following properties:
--   - it commutes with the antipodal map;
--   - it starts at the positive standard Hopf circle $H(u) = (u_1, 0, -u_2, 0)$;
--   - it ends at $N(\widetilde\delta)$;
--   - every circle stays positively transverse to the radial contact structure $\alpha_y(v) = -\tfrac12\,\omega(y,v)$.
--
--   This is the statement that the retrograde orbit is a Hopf fiber, i.e. a 2-unknot of rational self-linking number $-1/2$ in the antipodal quotient. It is phrased here in the Levi-Civita coordinates themselves, with no auxiliary regularization model.
--
--   **Proof outline.** In Levi-Civita coordinates $(z, w)$, the doubled lift projects to a simple closed curve $z(t)$ in $\mathbb{C}\setminus\{0\}$ with winding number one around $0$. Write $z = r e^{i\theta}$ and let the doubled period be $2P$. Over any such loop, the lift $w = Jz + (2\theta - \tfrac{2\pi}{P} t)\,z$ satisfies
--
--   $$
--   \alpha(\dot\gamma) = \tfrac{\pi}{P}\, r^2 > 0.
--   $$
--
--   It is embedded and antipodally equivariant, and transverse lifts over a fixed loop form a convex set. The orbit is a transverse lift because the subcritical component is star-shaped. This gives an explicit chain of equivariant transverse isotopies: the orbit, then the canonical lift, then a round circle, then a Hopf fiber, then $H$.
--
--   **Formalization note.** Transversality of the orbit itself uses the star-shapedness of the Levi-Civita regularized component below the first critical value, which remains part of the assertion.
-- source:
--   Hryniewicz--Salomao--Wysocki, arXiv:1912.01078v3, Section 1.3, paragraph after Definition 1.16 ('the retrograde orbit is a Hopf fiber, i.e., a 2-unknot with rational self-linking number -1/2'), https://arxiv.org/html/1912.01078v3; Hryniewicz--Salomao, arXiv:1505.02713v3, Section 1.3.1, https://arxiv.org/html/1505.02713v3. Star-shapedness of the Levi-Civita regularized component below the first critical value: Albers--Frauenfelder--van Koert--Paternain, The contact geometry of the restricted 3-body problem, Comm. Pure Appl. Math. 65 (2012), arXiv:1010.2140, https://arxiv.org/abs/1010.2140. Stated here in Levi-Civita coordinates, without a regularization model.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

namespace BirkhoffGlobalSection

/-- The normalized Levi-Civita double lift of a geometric Birkhoff retrograde
trajectory is equivariantly transversely isotopic to the positive standard
Hopf circle, for the radial contact structure of the round sphere. No
regularization model enters: this is the knot-type identification in the
Levi-Civita coordinates themselves. -/
theorem geometric_retrograde_leviCivita_transverse_hopf
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ) :
    Nonempty (EquivariantTransverseHopfIsotopy
      (radialNormalize '' orbitSet (antipodalTrajectoryDoubleLift φ hanti δ))) := by sorry

end BirkhoffGlobalSection
