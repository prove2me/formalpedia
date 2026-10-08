-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_Stationary_theorem_2
-- name    : BlackwellDiscreteDP.Stationary.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:01:30.61549+00:00
-- url     : https://prove2.me/theorems/3aa62779-c0cf-4574-a5dc-348a0723acc7
-- title:
--   Theorem 2 — if (f, π) > π, then f^(∞) > π
-- statement:
--   Fix $0\le\beta<1$. For vectors, $w_1>w_2$ means $w_1\ge w_2$ coordinatewise and $w_1\ne w_2$. Let $f$ be a decision rule and $\pi$ a policy. If
--
--   $$V_\beta(f,\pi)>V_\beta(\pi),$$
--
--   then
--
--   $$V_\beta(f^{(\infty)})>V_\beta(\pi).$$
--
--   If using $f$ for one day before $\pi$ is a strict improvement, then using $f$ forever is a strict improvement. It is the step of the policy improvement theorem (Theorem 3) that turns a one-step comparison into a comparison of stationary policies.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 720, Theorem 2

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- Theorem 2, p. 720 (Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"If (f, π) > π, then f^(∞) > π."

Both `>` are Blackwell's strict vector order (p. 720): `w₁ > w₂` iff `w₁ ≧ w₂` coordinatewise
and `w₁ ≠ w₂` (not coordinatewise strict). The discount factor is fixed, `0 ≤ β < 1`. -/
theorem theorem_2 {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act) (π : Policy St Act)
    (h : M.V β π ≤ M.V β (Policy.cons f π) ∧ M.V β (Policy.cons f π) ≠ M.V β π) :
    M.V β π ≤ M.V β (stationary f) ∧ M.V β (stationary f) ≠ M.V β π := by sorry

end BlackwellDiscreteDP.Stationary
