-- Prove2me | Theorems.Thm_ExtrapBias_Beliefs_extrapolation_bias
-- name    : ExtrapBias.Beliefs.extrapolation_bias
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:58.587047+00:00
-- url     : https://prove2.me/theorems/ccc3feb1-166d-40bc-9db0-cba1ca59618d
-- title:
--   §4.1, p. 21, corrected — worst-case beliefs and shock sensitivity signs
-- statement:
--   Let qᴬ be the positive ambiguity benchmark, m* the payout boundary, and F an increasing, concave C² solution of the scaled variational system (25)–(31). For each cash ratio m∈[0,m*], the angle φ(m) from (26) lies in (0,π/2) and uniquely minimizes the bracket (25) over φ∈[0,2π], for every investment i. Define hᴾ and hᵀ by (27). Their responses to permanent (P) and temporary (T) shocks have signs
--   $$
--   S_{PP}(m)\geq0,\qquad S_{PT}(m)\leq0,\qquad
--   S_{TP}(m)\leq0,\qquad S_{TT}(m)\geq0.
--   $$
--   When F″(m)<0, the temporary-shock signs are strict. If also m>0, the permanent-shock signs are strict. This is the model’s endogenous extrapolation-bias claim: worst-case beliefs react to recent shocks of each type.
--
--   **Formalization Note** The sensitivities are the four coefficients in the p. 21 display. The weak signs include m=0 and m=m*, where strict signs can fail. The printed p. 20 monotonicity sentence is reversed; the directions here agree with the p. 21 display. Positivity and the attained max-min convention are built into the shared model definitions.
-- source:
--   Lee & Rivera, Extrapolation Bias and Dynamic Liquidity Management, working paper (May 24, 2019), p. 21, §4.1 sensitivity display and conclusion; pp. 17–18, (25)–(27)

import Mathlib
import Definitions.Def_ExtrapBias_Beliefs_Model

namespace ExtrapBias.Beliefs

/-- §4.1, p. 21, with (26)–(27). The signs correct the p. 20
monotonicity slip; strict signs hold only at the nonflat interior points. -/
theorem extrapolation_bias (p : Params) (qA iA φA mstar : ℝ) (F : ℝ → ℝ)
    (hA : IsAmbBenchmark p qA iA φA)
    (hF : IsScaledValue p qA mstar F) :
    ∀ m ∈ Set.Icc 0 mstar,
      phiOpt p F m ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧
      (∀ i : ℝ, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i (phiOpt p F m) ≤
          bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i φ ∧
        (bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i φ =
          bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i (phiOpt p F m) →
          φ = phiOpt p F m)) ∧
      0 ≤ sensPP p F m ∧ sensPT p F m ≤ 0 ∧
      sensTP p F m ≤ 0 ∧ 0 ≤ sensTT p F m ∧
      (deriv (deriv F) m < 0 →
        sensPT p F m < 0 ∧ 0 < sensTT p F m ∧
        (0 < m → 0 < sensPP p F m ∧ sensTP p F m < 0)) := by sorry

end ExtrapBias.Beliefs
