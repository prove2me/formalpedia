-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_theorem_7_1
-- name    : AutobiddingGSP.Approximation.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:29:19.941354+00:00
-- url     : https://prove2.me/theorems/dcf144b7-363f-4692-bc43-ec9d5baf52ea
-- title:
--   Theorem 7.1 — ABE-B is PPAD-hard for every fixed 0 ≤ γ < 1, even with K = M and unit CTRs
-- statement:
--   For every fixed $0\le\gamma<1$, computing a γ-approximate ABE-B is PPAD-hard even when the number of slots equals the number of items and all click-through rates equal one; this holds with real answers (the multipliers of every γ-approximate equilibrium, including irrational exact ones at $\gamma=0$) and with rational answer codes.
--
--   Differences from the source:
--   - generalization: computing a γ-approximate ABE-B (α, π) → two forms: (i) real answers that are the multiplier vector α of any γ-approximate equilibrium (real α, real π), decoded through polynomially many exact comparisons with rationals; (ii) rational answer codes of (α, π); reason: the paper's decoding uses only α and applies to every valid π; a decoder from α is a decoder from (α, π), so (i) is at least as strong as hardness of computing (α, π)
--   - encoding: PPAD-hard → RealPPADHard (every PPAD problem reduces by RealSearchReduces) and CEPolytopeHard.PPADHard; reason: real-answer extension of the published search reductions, and the published finite-string one
--   - encoding: the number of slots equals the number of items and all click-through rates equal one → instances with ValidFor … true (K = M and every c_k = 1); reason: restricted instance class
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Theorem 7.1, p. 35 (PDF 35)

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_AutobiddingGSP_Approximation_Search

namespace AutobiddingGSP.Approximation

/-- **Theorem 7.1 (Restatement of Theorem 1.2, ABE-B hardness)** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 35 (PDF 35)). For every
fixed `0 ≤ γ < 1`, computing a γ-approximate ABE-B is PPAD-hard even when the number of slots
equals the number of items and all click-through rates equal one (`r = true`): both with real
answers (every γ-approximate equilibrium, possibly irrational, read through exact comparisons)
and with rational answer codes. -/
theorem theorem_7_1 (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    RealPPADHard (ABERealSearch Model.budget γ true) ∧
      CEPolytopeHard.PPADHard (ABESearch Model.budget (fun _ => γ) true) := by sorry

end AutobiddingGSP.Approximation
