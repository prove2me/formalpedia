-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_bounded_input_gcircuit_hard
-- name    : CorrelatedAuctionComplexity.Main.bounded_input_gcircuit_hard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:04.10421+00:00
-- url     : https://prove2.me/theorems/1e60d50d-af6a-4a6e-b265-26aa18391b13
-- title:
--   Theorem 7 — Bounded-input SUM/NOT circuit hardness
-- statement:
--   There is a fixed positive approximation constant $\varepsilon$ for which finding a solution to a generalized circuit with only saturated SUM and NOT gates is PPAD-hard, even when every node is used as an input of at most two gates:
--
--   $$\exists\varepsilon>0,\quad\varepsilon\text{-GCircuit}_{\{\mathrm{SUM},\mathrm{NOT}\},\,\mathrm{input\ use}\le2}\text{ is PPAD-hard}.$$
--
--   The solution domain is $[0,1+\varepsilon]^V$. A SUM can repeat its input; that gate counts only once toward input use. This supplies the unconditional hardness starting point.
--
--   Differences from the source:
--   - encoding: a generalized circuit given explicitly and an ε-approximate solution listed as real node values → canonical self-delimiting binary circuit records and rational node assignments with the polynomial witnessBound on answer length; reason: standard finite search representation; a target-side answer restriction only makes PPAD-hardness easier to inherit, and every assignment from a reduction is a polynomially long rational record
--   - encoding: there exists a fixed real approximation constant greater than zero → there exists a fixed positive rational approximation constant before any instance; reason: a smaller positive rational tolerance is admissible by density and monotonicity of approximation; all input instances and the restricted hardness clause are retained
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Theorem 7, p. 12 (PDF p. 12)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem bounded_input_gcircuit_hard :
    ∃ ε : ℚ, 0 < ε ∧ PPADHard (gcircuitSearch ε) := by sorry

end CorrelatedAuctionComplexity.Main
