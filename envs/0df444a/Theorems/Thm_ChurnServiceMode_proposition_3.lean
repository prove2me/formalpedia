-- Prove2me | Theorems.Thm_ChurnServiceMode_proposition_3
-- name    : ChurnServiceMode.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:48.004973+00:00
-- url     : https://prove2.me/theorems/4c431fe1-7a3c-48dc-b3c1-d4debcde657b
-- title:
--   Proposition 3 — the candidate $W^*$ satisfies the conditions of Proposition 2 (corrected: sign of the erf difference in Lemma 3's (11))
-- statement:
--   Assume $q>\mu_S$ (Assumption 1), and let $\theta_b$ and $\theta_G$ be the thresholds of Lemmas 2 and 3. Then there exist constants $C_1^*,\dots,C_5^*$ such that
--   $$W^*(\cdot)=W(\cdot,C_1^*,C_2^*,C_3^*,C_4^*,C_5^*)$$
--   (the function glued from $V_1,\dots,V_4$ of displays (18)–(21)), together with the policy of Theorem 1, satisfies all six conditions of Proposition 2.
--
--   With Proposition 2 this gives Theorem 1.
--
--   Differences from the source:
--   - correction: display (11) of Lemma 3 contains (erf((q−µR)/σR) − erf((θ−µR)/σR)) → smallFn uses (erf((θ−µR)/σR) − erf((q−µR)/σR)); reason: the printed Lemma 3 is false: at (µS, µR, σR, q) = (5, 1, 3, 6) the printed union is {5.59957, 4.48080}, two elements; at (2, 1, 1, 3) the printed θG = 2.94588 gives a policy with V(3) = 2.0945 < 2.2964 for θ = 2.59275, the root of the corrected equation; the proof of Lemma 3 (p.24) defines F_small with (erf θ̂ − erf q̂) and says it is twice the LHS of (11)
--   - reading: Assumption 1 (q > µS), imposed "throughout this paper" (p.8) and not repeated in the statement → hypothesis μS < q; reason: standing assumption of the paper; the constant term of (11)–(12) divides by q − µS
--   - encoding: θb = ∞, θG = −∞; V₁(x, C₁) = C₁/(x − µS) + µS → EReal thresholds; Lean value C₁/0 = 0 at x = µS; reason: x = µS lies in the region x ≤ θG only when θG ≥ µS, where continuous differentiability forces C₁* = 0, so W is the paper's function
--   - reading: σ_R (the Risky volatility; positivity never displayed) → 0 < σR (field of Params); reason: every formula of Lemmas 2–3 and Proposition 3 divides by σ_R, and σ_R is called a volatility
--   - reading: "twice continuously differentiable on ℝ∖E" for a countable E (ℝ∖E need not be open); V′, V″ → deriv V differentiable at every point off E and deriv (deriv V) continuous on Eᶜ (relative topology); V′ = deriv V, V″ = deriv (deriv V); reason: the pointwise reading of C² on a set that need not be open; when E is closed (for W*, E ⊆ {θG, q, θb}) it is C² on the open set ℝ∖E
--   - generalization: Conditions 5–6 of Proposition 2 for the process H^{x,π̄} of the Theorem 1 policy → Prop2Conditions: Conditions 5–6 for every π̄-feedback ControlSystem started at x, on any filtered probability space; reason: the paper's process is one such system, so the conclusion specializes to the paper's; it also covers solutions whose law is not unique (Lemma 1 correction)
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Proposition 3, displays (18)–(21), p.20 (PDF p.20); explicit constants (36)–(38), pp.27–28, and OA B, PDF pp.40–41

import Mathlib
import Definitions.Def_ChurnServiceMode_Prop2Conditions
import Definitions.Def_ChurnServiceMode_optPolicy
import Definitions.Def_ChurnServiceMode_candidateValue

open MeasureTheory ProbabilityTheory Filter PeskirShiryaev.LocalTime
open scoped NNReal ENNReal Topology

namespace ChurnServiceMode

/-- **Proposition 3** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.20; with Lemma 3's corrected display (11)). Under Assumption 1
(`q > μS`), let `θb` and `θG` be the thresholds of Lemmas 2 and 3. Then there are constants
`C₁*, …, C₅*` such that `W*(·) = W(·, C₁*, …, C₅*)` together with the policy of Theorem 1
satisfies all the conditions of Proposition 2. -/
theorem proposition_3 (p : Params) (hq : p.μS < p.q) (θb θG : EReal) (hb : IsThetaB p θb)
    (hG : IsThetaG p θG) :
    ∃ C₁ C₂ C₃ C₄ C₅ : ℝ,
      Prop2Conditions p (W p θb θG C₁ C₂ C₃ C₄ C₅) (optPolicy p θb θG) := by sorry

end ChurnServiceMode
