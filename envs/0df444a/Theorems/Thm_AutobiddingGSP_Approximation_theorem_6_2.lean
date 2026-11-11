-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_theorem_6_2
-- name    : AutobiddingGSP.Approximation.theorem_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:27:38.355345+00:00
-- url     : https://prove2.me/theorems/da9425bc-abc7-45b0-a2f3-1245fefeca81
-- title:
--   Theorem 6.2 — Bounded-Forward-Span Pure-Circuit(5) is PPAD-hard
-- statement:
--   Bounded-Forward-Span Pure-Circuit(5) — Pure-Circuit instances with a gate ordering of forward span at most five (backward spans and fan-out unrestricted), asking for a satisfying assignment — is PPAD-hard.
--
--   Differences from the source:
--   - reading: Pure-Circuit instances of Definition 6.2 → instances whose gates' outputs are distinct from their inputs; reason: the convention stated and used in §7.2 p. 33 and §8.2 p. 39; the construction of the proof has it, and hardness for these instances implies hardness without the restriction
--   - encoding: an instance together with an ordering of its gates → the gate list in that order; codes in self-delimiting binary; reason: the order is part of the input
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Theorem 6.2, p. 29 (PDF 29); proof pp. 29–30

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_AutobiddingGSP_Approximation_PureCircuit

namespace AutobiddingGSP.Approximation

/-- **Theorem 6.2** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 29 (PDF 29)). Bounded-Forward-Span Pure-Circuit(5) is PPAD-hard: the
instances carry a gate ordering with every forward span at most five; backward spans and fan-out
are unrestricted. -/
theorem theorem_6_2 : CEPolytopeHard.PPADHard (BFSPC 5) := by sorry

end AutobiddingGSP.Approximation
