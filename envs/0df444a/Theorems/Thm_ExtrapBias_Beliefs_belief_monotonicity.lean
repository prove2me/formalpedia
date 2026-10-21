-- Prove2me | Theorems.Thm_ExtrapBias_Beliefs_belief_monotonicity
-- name    : ExtrapBias.Beliefs.belief_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:04.599395+00:00
-- url     : https://prove2.me/theorems/388b2a13-74b2-4d02-a2e1-41eb478ae1aa
-- title:
--   §4.1, p. 20, corrected — hᴾ falls and hᵀ rises as cash increases
-- statement:
--   Let qᴬ be the ambiguity-only benchmark and F an increasing, concave, twice continuously differentiable solution of the scaled cash-management system. On the no-payout interval [0,m*], the worst-case angle φ(m) is nonincreasing. So are the permanent-shock distortions hᴾ(m), while the temporary-shock distortions hᵀ(m) are nondecreasing:
--   $$
--   m_1\leq m_2\quad\Longrightarrow\quad
--   \phi(m_2)\leq\phi(m_1),\quad
--   h^P(m_2)\leq h^P(m_1),\quad
--   h^T(m_1)\leq h^T(m_2).
--   $$
--   More cash therefore shifts the adverse drift toward permanent shocks and away from temporary shocks.
--
--   **Formalization Note** The working paper’s final sentence on p. 20 reverses the directions. The statement follows the paragraph’s economic description and the sensitivity signs on p. 21.
-- source:
--   Lee & Rivera, Extrapolation Bias and Dynamic Liquidity Management, working paper (May 24, 2019), p. 20, §4.1, final monotonicity paragraph; p. 21, sensitivity display

import Mathlib
import Definitions.Def_ExtrapBias_Beliefs_Model

namespace ExtrapBias.Beliefs

/-- §4.1, p. 20, corrected directions: as cash rises, the worst
permanent-shock drift falls and the worst temporary-shock drift rises. -/
theorem belief_monotonicity (p : Params) (qA iA φA mstar : ℝ) (F : ℝ → ℝ)
    (hA : IsAmbBenchmark p qA iA φA)
    (hF : IsScaledValue p qA mstar F) :
    AntitoneOn (phiOpt p F) (Set.Icc 0 mstar) ∧
    AntitoneOn (hP p F) (Set.Icc 0 mstar) ∧
    MonotoneOn (hT p F) (Set.Icc 0 mstar) := by sorry

end ExtrapBias.Beliefs
