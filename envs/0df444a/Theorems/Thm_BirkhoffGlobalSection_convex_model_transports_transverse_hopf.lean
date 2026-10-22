-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_transports_transverse_hopf
-- name    : BirkhoffGlobalSection.convex_model_transports_transverse_hopf
-- status  : Open
-- author  : @caleb
-- created : 2026-10-01T01:06:52.219549+00:00
-- url     : https://prove2.me/theorems/f7c5a998-6bbc-4ef2-a169-fabd06647d10
-- title:
--   Regularization models preserve the transverse Hopf class
-- statement:
--   Let $0<\mu<1$ and let the Jacobi value lie below the first critical value. Let $M$ be a convex conformally symplectic regularization model of the selected left energy component, with coordinate map $F$. Let $\gamma$ be a closed orbit of the Levi-Civita Hamiltonian flow on that component. Write $N(y) = y/|y|$ for radial normalization onto the round sphere. If the normalized orbit $N(\gamma)$ is equivariantly transversely isotopic to the positive standard Hopf circle, then so is the normalized model image:
--
--   $$
--   \operatorname{Nonempty}\bigl(\operatorname{EquivariantTransverseHopfIsotopy}(N(\gamma))\bigr)
--   \;\Longrightarrow\;
--   \operatorname{Nonempty}\Bigl(\operatorname{EquivariantTransverseHopfIsotopy}\bigl(N(F(\gamma))\bigr)\Bigr).
--   $$
--
--   This is the independence of the transverse knot class from the choice of regularization.
--
--   **Why it holds.** Radial projection is a conformal contactomorphism from a star-shaped hypersurface, carrying its radial contact form, onto the standard sphere. The Levi-Civita component is star-shaped below the first critical value, and the model surface is the boundary of a convex body. Since $F^*\omega = \kappa\,\omega$ with $\kappa > 0$, the forms $F^*\alpha$ and $\kappa\alpha$ differ by a closed form. Both forms evaluate with one sign on the characteristic direction, so their convex combinations are contact forms. Gray stability, made antipodally equivariant, then transports the transverse isotopy class of $N(\gamma)$ to that of $N(F(\gamma))$. Coorientation reversal is handled by the antipodally equivariant reflection $(q, p) \mapsto (q, -p)$, which maps the standard Hopf circle to itself with reversed orientation.
--
--   **Formalization note.** The hypotheses $0 < \mu < 1$ and the subcritical energy are kept, so that the Levi-Civita component is star-shaped and its radial contact structure is defined.
-- source:
--   Independence of the transverse knot type from the choice of regularization, implicit in Hryniewicz--Salomao, arXiv:1505.02713v3, Section 1.3.1, https://arxiv.org/html/1505.02713v3, where the retrograde orbit is identified in (RP^3, xi_0) for any regularization. Standard tools: Gray stability (Geiges, An Introduction to Contact Topology, Theorem 2.2.2) and radial projection of star-shaped hypersurfaces; star-shapedness below the first critical value from Albers--Frauenfelder--van Koert--Paternain, arXiv:1010.2140, https://arxiv.org/abs/1010.2140.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

namespace BirkhoffGlobalSection

/-- Changing the regularization does not change the transverse Hopf class of a
closed Levi-Civita orbit. If the radial normalization of a closed orbit on the
selected subcritical component is equivariantly transversely isotopic to the
positive standard Hopf circle, then so is the radial normalization of its image
under any convex regularization model. -/
theorem convex_model_transports_transverse_hopf
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (γ : PeriodicOrbit φ)
    (hI : Nonempty (EquivariantTransverseHopfIsotopy (radialNormalize '' orbitSet γ))) :
    Nonempty (EquivariantTransverseHopfIsotopy
      (radialNormalize '' (M.toModel '' orbitSet γ))) := by sorry

end BirkhoffGlobalSection
