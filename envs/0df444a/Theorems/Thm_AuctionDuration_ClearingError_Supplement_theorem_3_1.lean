-- Prove2me | Theorems.Thm_AuctionDuration_ClearingError_Supplement_theorem_3_1
-- name    : AuctionDuration.ClearingError.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:49:26.876359+00:00
-- url     : https://prove2.me/theorems/d5057ba7-da0e-4e0d-a585-0982e482bc24
-- title:
--   Theorem 3.1 — Markovian Nash equilibrium with both attained best responses
-- statement:
--   Fix $h\ge0$, $0<\lambda_-\le\lambda_+$ and a reference rate $0<\lambda_0<\lambda_+$. The two canonical reference counts are independent Poisson processes. Each player chooses any predictable intensity in $[\lambda_-,\lambda_+]$ and the resulting law is the exponential likelihood law. For every initial state $x=(\alpha,\beta)\in\mathbb N^2$, let $V^{i,x}_h(a,b)$ be the expected terminal cost $g^i(x+X_h)$, where $g^a(y)=y_a(y_a-y_b)$ and $g^b(y)=y_b(y_b-y_a)$.
--
--   There is one pair of deterministic measurable feedback controls $(a^*,b^*)$, admissible from every initial state, such that both best responses are attained:
--   $$
--   \inf_{a\in\mathcal U}V^{a,x}_h(a,b^*)=V^{a,x}_h(a^*,b^*),\qquad
--   \inf_{b\in\mathcal U}V^{b,x}_h(a^*,b)=V^{b,x}_h(a^*,b^*)\quad(x\in\mathbb N^2).
--   $$
--   All controlled laws are probabilities and all these terminal costs are integrable. The equilibrium need not be unique. This is the strategic-market-taker companion theorem; it is not used to prove the mission's referenced clearing-price formula.
--
--   Differences from the source:
--   - reading: canonical compensated pair on p.23 → independent reference Poisson coordinates; reason: the multivariate point-process construction and signed compound-Poisson representation on p.29 use no common jumps; compensators alone would not fix a unique law
--   - encoding: predictable controls and current counts in feedbacks → all bounded predictable deviations and pre-jump count feedbacks; reason: pre-jump evaluation supplies predictable representatives and changes no dt×P equivalence class
--   - encoding: expected terminal costs under controlled probabilities → likelihood-defined laws plus probability and integrability conclusions; reason: the expectations are genuine, rather than default integrals of nonintegrable functions
--   - generalization: Appendix C fixes h>0 → h≥0; reason: at h=0 counts cannot move, the likelihood is one and every admissible pair minimizes the fixed terminal costs; the positive-horizon theorem is included
--   - encoding: infimum identities → IsLeast for each real cost set; reason: this gives both the printed infimum equality and attainment, without an empty or unbounded real-infimum default
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, https://arxiv.org/abs/1906.01713v3, p.13, Theorem 3.1; pp.12,22–24, governing game

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Supplement_StrategicGame

namespace AuctionDuration.ClearingError.Supplement

/-- Theorem 3.1 (arXiv:1906.01713v3, p.13): simultaneous attained
best responses, from every natural count pair, against all predictable deviations.
The zero-duration case is the deterministic terminal-cost extension. -/
theorem theorem_3_1 (G : Game) (hG : G.Standing) :
    G.WellDefined ∧ ∃ fa fb : ValueField, G.IsNash fa fb := by sorry

end AuctionDuration.ClearingError.Supplement
