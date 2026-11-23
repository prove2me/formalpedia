-- Prove2me | Theorems.Thm_CapitationRisk_PerfectRA_Supplement_theorem_4
-- name    : CapitationRisk.PerfectRA.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:41:17.160126+00:00
-- url     : https://prove2.me/theorems/a68ef625-a25c-4943-8234-9274a7a55d52
-- title:
--   Theorem 4 — additive demand preserves all equilibrium qualities under MLR
-- statement:
--   For the published model under Standing, suppose the full additive-demand specification (20)–(21) holds for populations Λ_i and probabilities ξ_is, with ∑_s ξ_is=1. Let E(r,w) denote direct quality optimization (35), and L(r,w,P) optimal provider-response pairs subject to MLR (34). Both problems attain their optima, and
--   $$E(r,w)\ \Longleftrightarrow\ \exists P\ L(r,w,P)\qquad\text{for every }w.$$
--   Thus every unconstrained optimal quality admits an MLR-feasible optimal implementing price vector, and every MLR optimum projects to an unconstrained optimal quality. The comparison preserves boundary optima and all services and types; it compares qualities without claiming a unique price vector. It is a companion theorem to the published goal, supported by Proposition 2.
--
--   Differences from the source:
--   - encoding: The source gives twice differentiable demands and costs on the quality box, patient counts and nonzero denominators implicitly. → The imported Standing context uses C² functions on the whole space, nonnegative service demands, positive target enrollment and positive target marginal service demand; finite types include Nonempty I.; reason: These are the published base conventions, reused without alteration; the stronger smoothness convention resolves endpoint derivatives and positive denominators resolve (3), (7) and the Bayes formula.
--   - reading: Theorem 4 cites the additive form (21). → Both (20) and (21), with nonnegative populations and normalized service-need probabilities, hold on the full source domains.; reason: Equation (21) explicitly equals the sum of the service demands specified by (20), not an unrelated additive plan-demand function. No individual probability is required to be positive.
--   - encoding: The MLR problem yields the same equilibrium quality as the unconstrained problem. → Both optimization problems attain their optima, and their projected optimizer sets coincide in both directions with existential prices.; reason: Global provider argmax constraints cover both endpoints without the interior FOC and multiplier identifications in (42)–(46). No black-swan or additional interiority premise is imposed.
--   - generalization: The fixed rates are interpreted as capitation payments. → The vector r can have arbitrary real entries.; reason: Under (20)–(21), each service has a linear revenue term, so the provider objective at a demand-weighted price equals its plan-profit summand for any signed rates. The equality and attainment therefore do not need a sign assumption.
--   - generalization: Section 5.3 assumes a nonempty black-swan set (8) for the paper’s model. → No BlackSwan premise is imposed on this result.; reason: The conclusion holds for every model satisfying Standing, including models with an empty black-swan set. The fixed-price provider maximization for Theorem 3, optimal-quality implementation for Proposition 2, and additive weighted-price construction for Theorem 4 do not use (8). Every source instance remains included.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), p. 41, Theorem 4; pp. 24–25, (20)–(21); pp. 39–43, (34)–(46)

import Definitions.Def_CapitationRisk_PerfectRA_Supplement_MLR
import Definitions.Def_CapitationRisk_PerfectRA_Supplement_AdditiveDemand

namespace CapitationRisk.PerfectRA.Supplement

theorem theorem_4 {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [Nonempty I]
    (M : Model S I) (hM : M.Standing) (r : I → ℝ)
    (population : I → ℝ) (need : I → S → ℝ)
    (hA : AdditiveDemand M population need) :
    (∃ w, M.IsMAEquilibrium r w) ∧
    (∃ w P, IsMLREquilibrium M r w P) ∧
    ∀ w, M.IsMAEquilibrium r w ↔ ∃ P, IsMLREquilibrium M r w P := by sorry

end CapitationRisk.PerfectRA.Supplement
