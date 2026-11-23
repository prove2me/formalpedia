-- Prove2me | Theorems.Thm_CapitationRisk_PerfectRA_Supplement_theorem_3
-- name    : CapitationRisk.PerfectRA.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:39:50.078559+00:00
-- url     : https://prove2.me/theorems/ffbeed27-1569-4f81-aabe-3e333a3cb452
-- title:
--   Theorem 3 — fixed-price contracting uniquely attains the target (corrected: P* in (16))
-- statement:
--   For the published model under Standing, use the exact rates r* of (7) and add the single aggregate restriction (16), evaluated at fixed exogenous TM prices P*. Then
--   $$w^*\in\operatorname*{argmax}_{w\in F_{16}}\pi(r^*,w),\qquad\operatorname*{argmax}_{w\in F_{16}}\pi(r^*,w)=\{w^*\}.$$
--   Here F_16 is the quality box intersected with ∑_i λ_i(w)r*_i=∑_s D_s(w_s)P*_s. Target feasibility and attainment are asserted, and every global maximizer has the target quality in every service. This eliminates risk selection in the paper's sense of quality distortion relative to w*; equality of objective values alone is not the claim.
--
--   Differences from the source:
--   - encoding: The source gives twice differentiable demands and costs on the quality box, patient counts and nonzero denominators implicitly. → The imported Standing context uses C² functions on the whole space, nonnegative service demands, positive target enrollment and positive target marginal service demand; finite types include Nonempty I.; reason: These are the published base conventions, reused without alteration; the stronger smoothness convention resolves endpoint derivatives and positive denominators resolve (3), (7) and the Bayes formula.
--   - correction: The first display (16) uses P_s without a star. → The aggregate constraint uses the fixed vector P*_s=M.TMPrice s (w*_s).; reason: The text immediately following (16), the next constrained problem, and (31)–(33) all specify exogenous P*. No domain cases are excluded.
--   - reading: The mechanism achieves the benchmark and eliminates risk selection. → The target is a feasible attained global maximum and all maximizers equal it.; reason: The source proof identifies the optimizers in (31)–(33); the paper defines the relevant selection through service-quality deviations. No black-swan assumption or interior upper bound is added.
--   - generalization: Section 5.3 assumes a nonempty black-swan set (8) for the paper’s model. → No BlackSwan premise is imposed on this result.; reason: The conclusion holds for every model satisfying Standing, including models with an empty black-swan set. The fixed-price provider maximization for Theorem 3, optimal-quality implementation for Proposition 2, and additive weighted-price construction for Theorem 4 do not use (8). Every source instance remains included.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), p. 22, Theorem 3; pp. 21, 38–39, (16), (31)–(33)

import Definitions.Def_CapitationRisk_PerfectRA_Supplement_SelectionProof

namespace CapitationRisk.PerfectRA.Supplement

theorem theorem_3 {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [Nonempty I]
    (M : Model S I) (hM : M.Standing) :
    IsSelectionEquilibrium M M.rate M.wstar ∧
    ∀ w, IsSelectionEquilibrium M M.rate w → w = M.wstar := by sorry

end CapitationRisk.PerfectRA.Supplement
