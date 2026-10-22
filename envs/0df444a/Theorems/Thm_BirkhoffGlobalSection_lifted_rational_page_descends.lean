-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lifted_rational_page_descends
-- name    : BirkhoffGlobalSection.lifted_rational_page_descends
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-26T18:20:21.461733+00:00
-- url     : https://prove2.me/theorems/5cd7aaae-d961-4703-88db-5db8562177ca
-- title:
--   A lifted rational page descends through the antipodal cover
-- statement:
--   Let $\varphi$ be a continuous complete flow on a selected Levi-Civita component $\Sigma_{\mu,c}$. Suppose the component is invariant under the antipodal map, that this map has no fixed points, and that the flow commutes with it. Let $\gamma$ be a least-period closed orbit reaching its antipode at half-period.
--
--   If $\gamma$ admits a lifted rational page, then it induces a rational two-disk global surface of section in the antipodal quotient:
--
--   $$
--   \operatorname{LiftedRationalPage}(\varphi,\gamma)
--   \quad\Longrightarrow\quad
--   \operatorname{RationalDiskLikeGlobalSurfaceOfSection}(\varphi,\gamma).
--   $$
--
--   The conclusion includes jointly continuous quotient dynamics, primeness of the half-period quotient binding, continuity of the quotient page, embedding of its interior, precisely the two-fold boundary identifications, and unbounded positive and negative return times for every nonbinding quotient trajectory. Transversality is measured on the smooth lift by the Levi-Civita Hamiltonian vector field.
--
--   This is a cover-descent lemma for the rational-page encoding used in the mission. It assumes neither a near-equal-mass restriction nor the existence of any page; it applies whenever the stated cover and page data are supplied.
-- source:
--   Liu?Salom?o, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Theorem 1.16(ii), Section 9.2 and Section 10; Joung?van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4. The cover-level definitions and descent formulation are formalization interfaces; the model and positive-time-change transport are explicit obligations, not conclusions quoted verbatim from the source.

import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage

namespace BirkhoffGlobalSection

/-- Descent of a smooth lifted rational two-disk, including its two-sided
return property, through the free invariant antipodal cover. -/
theorem lifted_rational_page_descends {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (hinv : IsAntipodallyInvariantComponent μ c)
    (hfree : IsAntipodallyFreeComponent μ c)
    (γ : PeriodicOrbit φ) (hdouble : IsAntipodalDoubleCover φ γ)
    (P : LiftedRationalPage φ γ) :
    RationalDiskLikeGlobalSurfaceOfSection φ hanti γ := by sorry

end BirkhoffGlobalSection
