-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_Supplement_theorem_2_1
-- name    : BicliqueSDP.Chain.Supplement.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:16:02.811252+00:00
-- url     : https://prove2.me/theorems/6806d868-667c-442a-80c0-110766ffe46c
-- title:
--   Theorem 2.1 — α-BAL-BIP is NP-complete
-- statement:
--   For finite bipartite graphs with their two parts specified, deciding whether a maximum independent set can be balanced is NP-complete:
--
--   $$\alpha\text{-}\mathrm{BAL}\text{-}\mathrm{BIP}\in\mathrm{NP},\qquad \forall L\in\mathrm{NP},\quad L\le_P\alpha\text{-}\mathrm{BAL}\text{-}\mathrm{BIP}.$$
--
--   Balanced means that the independent set contains equally many vertices from each fixed part. Both NP membership and NP hardness are required. This is the complexity companion to the semidefinite inequalities in the goal.
--
--   Differences from the source:
--   - encoding: The source uses graph instances and standard polynomial-time algorithms → The statement uses the fixed dense bipartite codes and CookPvsNP.NPComplete; reason: The encoding includes both sides and is polynomially reasonable; the imported definition includes NP membership and reductions from every NP language over every finite nonempty alphabet.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 7, Theorem 2.1

import Definitions.Def_BicliqueSDP_Chain_Supplement_Problems
set_option autoImplicit false

namespace BicliqueSDP.Chain.Supplement

/-- Theorem 2.1: BOTH NP membership and hardness, with a step-count complexity model. -/
theorem theorem_2_1 : CookPvsNP.NPComplete alphaBalBip := by sorry

end BicliqueSDP.Chain.Supplement
