-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_theorem_6_1
-- name    : AutobiddingGSP.Approximation.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:27:49.373965+00:00
-- url     : https://prove2.me/theorems/ff515e45-519e-4922-967a-117a248e05c8
-- title:
--   Theorem 6.1 — 2D Strong Sperner is PPAD-hard
-- statement:
--   The 2D Strong Sperner problem of Definition 6.1 (grid side $2^b$, labeling by a Boolean circuit, both labels must differ) is PPAD-hard: every problem of PPAD reduces to it by a polynomial-time search reduction.
--
--   Differences from the source:
--   - encoding: a Boolean circuit with 2b input bits and two output bits representing C : {0..2^b−1}² → {0,1}² → a published ConstrSOSP.Circuit (∧, ∨, ¬) with 2b inputs (bits of p₁ then p₂, most significant first) and two outputs; points and answers in self-delimiting binary; reason: the paper fixes no bit order or code
--   - encoding: PPAD-hard → CEPolytopeHard.PPADHard (every problem of QuasiStrictNE.PPAD reduces by CardinalMatching.SearchReduces); reason: published definitions of PPAD and search reductions
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Theorem 6.1, p. 26 (PDF 26)

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_AutobiddingGSP_Approximation_StrongSperner

namespace AutobiddingGSP.Approximation

/-- **Theorem 6.1** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 26 (PDF 26)). The 2D Strong Sperner problem (Definition 6.1, p. 25:
grid side `2^b`, labeling given by a Boolean circuit with `2b` input bits and two output bits)
is PPAD-hard. -/
theorem theorem_6_1 : CEPolytopeHard.PPADHard StrongSperner2D := by sorry

end AutobiddingGSP.Approximation
