-- Prove2me | Theorems.Thm_CapitationRisk_PerfectRA_Supplement_proposition_2
-- name    : CapitationRisk.PerfectRA.Supplement.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:40:47.416277+00:00
-- url     : https://prove2.me/theorems/0e2789ba-c9b3-4069-9d15-c6517542c3dd
-- title:
--   Proposition 2 — direct and two-stage quality optimization have the same attained outcomes
-- statement:
--   For the published model under Standing and fixed capitation rates r, let E(r,w) denote direct global quality optimization (35) and T(r,w,P) denote optimal provider-response pairs for (36). Both problems attain their optima, and
--   $$E(r,w)\ \Longleftrightarrow\ \exists P\ T(r,w,P)\qquad\text{for every quality vector }w.$$
--   Every direct optimum therefore lifts to a two-stage optimum, and every two-stage optimum projects to a direct optimum. Prices are existentially quantified and need not be unique. This is the general result supporting Theorem 4, without an additive-demand or interior-quality restriction.
--
--   Differences from the source:
--   - encoding: The source gives twice differentiable demands and costs on the quality box, patient counts and nonzero denominators implicitly. → The imported Standing context uses C² functions on the whole space, nonnegative service demands, positive target enrollment and positive target marginal service demand; finite types include Nonempty I.; reason: These are the published base conventions, reused without alteration; the stronger smoothness convention resolves endpoint derivatives and positive denominators resolve (3), (7) and the Bayes formula.
--   - encoding: Same equilibrium quality in (35) and (36). → Nonempty optimizer sets and both directions of the projected optimizer correspondence, using full interval provider argmax sets.; reason: This states equality of attained quality outcomes, rather than only equality of values or first-order conditions. Neither price uniqueness nor implementability of every nonoptimal quality is assumed.
--   - generalization: The rates are capitation payments; no sign condition is displayed in (35)–(36). → The fixed vector r may have any real entries.; reason: Compactness gives direct attainment even for signed r. Provider implementation at an optimal quality uses the source option-demand bound and monotonic fixed costs, not nonnegativity of r; see the endpoint analysis in MODERATION_NOTES.md.
--   - generalization: Section 5.3 assumes a nonempty black-swan set (8) for the paper’s model. → No BlackSwan premise is imposed on this result.; reason: The conclusion holds for every model satisfying Standing, including models with an empty black-swan set. The fixed-price provider maximization for Theorem 3, optimal-quality implementation for Proposition 2, and additive weighted-price construction for Theorem 4 do not use (8). Every source instance remains included.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), pp. 40–42, Proposition 2, (35)–(36), (39)–(40)

import Definitions.Def_CapitationRisk_PerfectRA_Supplement_ProviderResponse

namespace CapitationRisk.PerfectRA.Supplement

theorem proposition_2 {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [Nonempty I]
    (M : Model S I) (hM : M.Standing) (r : I → ℝ) :
    (∃ w, M.IsMAEquilibrium r w) ∧
    (∃ w P, IsTwoStageEquilibrium M r w P) ∧
    ∀ w, M.IsMAEquilibrium r w ↔ ∃ P, IsTwoStageEquilibrium M r w P := by sorry

end CapitationRisk.PerfectRA.Supplement
