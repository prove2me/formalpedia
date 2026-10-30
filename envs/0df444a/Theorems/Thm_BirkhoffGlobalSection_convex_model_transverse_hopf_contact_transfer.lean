-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_transverse_hopf_contact_transfer
-- name    : BirkhoffGlobalSection.convex_model_transverse_hopf_contact_transfer
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T22:09:48.019329+00:00
-- url     : https://prove2.me/theorems/767fe11d-742c-47c0-b881-b128a44e511b
-- title:
--   Regularization transport up to an equivariant contactomorphism
-- statement:
--   Let $0<\mu<1$ and let $c$ lie below the first critical value. Let $M$ be a convex regularization model for the selected Levi-Civita component, let $\phi$ be its Levi-Civita Hamiltonian flow, and let $\gamma$ be any periodic orbit. Write $N$ for radial normalization to the unit three-sphere.
--
--   Suppose $N(\gamma)$ admits a smooth antipodal-equivariant, positively transverse isotopy from the fixed standard Hopf circle. Then there are a subset $K\subset S^3$ and a coorientation-preserving contactomorphism $F$ of the standard contact sphere, commuting with the antipodal map, such that
--
--   $$K\text{ admits an equivariant transverse Hopf isotopy},\qquad F(K)=N(M(\gamma)).$$
--
--   The recorded period of $\gamma$ need not be its least period. This theorem supplies the analytic transport by an equivariant contactomorphism. Identifying its image with the fixed standard Hopf transverse isotopy class requires the separate topological invariance statement; that assertion is not included here.
-- source:
--   Derived analytic transport lemma for https://prove2.me/theorems/f7c5a998-6bbc-4ef2-a169-fabd06647d10. Gray/Moser input: Geiges, Contact geometry, https://arxiv.org/abs/math/0307242v2, Theorem 2.20, printed pp. 14-15, equations (2.1)-(2.2); the antipodal averaging and periodic-orbit local-coordinate argument are supplied in the proof. Geometric context: Hryniewicz-Salomao, https://arxiv.org/abs/1505.02713v3, Section 1.3.1. This is a derived supporting lemma, not a verbatim numbered theorem or a claim of contact-group connectedness. The sphere/regular-level bridge reuses the accepted equivariant transverse-isotopy extension source, submission ea478b17-3193-4ab9-beae-b6d3f824d4f7; the source radial chart is proved by submission a97860d1-b720-4790-92ae-267db224327c.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection
open scoped ContDiff

theorem BirkhoffGlobalSection.convex_model_transverse_hopf_contact_transfer
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (γ : PeriodicOrbit φ)
    (hI : Nonempty (EquivariantTransverseHopfIsotopy (radialNormalize '' orbitSet γ))) :
    ∃ K : Set Phase, ∃ F : EquivariantSphereContactomorphism,
      Nonempty (EquivariantTransverseHopfIsotopy K) ∧
      F.toFun '' K = radialNormalize '' (M.toModel '' orbitSet γ) := by sorry
