-- Prove2me | Theorems.Thm_FixpReciprocal_solution_exists
-- name    : FixpReciprocal.solution_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:49:44.125206+00:00
-- url     : https://prove2.me/theorems/7d549852-4720-4eda-8fb9-a51a84de5492
-- title:
--   §1 and footnote 4 — every generalized circuit with the gates of (1) has a solution
-- statement:
--   For every rational $\tau>0$, every generalized circuit with the gates of (1) has a solution. The right-hand sides define a continuous self-map of $[0,1]^N$, so this follows from Brouwer's fixed-point theorem.
--
--   The main theorem's proof does not use this. It shows the search problem is total, so hardness is not vacuous.
--
--   Differences from the source: none.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), §1, p.2 (PDF p.4); footnote 4, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_FixpReciprocal_RGate

namespace FixpReciprocal

/-- **A solution exists.** "The right-hand sides define a continuous self-map of `[0, 1]^N`, so a solution exists
by Brouwer's fixed-point theorem."

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), §1, p.2; footnote 4, p.11. -/
theorem solution_exists (τ : ℚ) (hτ : 0 < τ) (C : List RGate) (hC : RValid C) :
    (RCircuitSol τ C).Nonempty := by sorry

end FixpReciprocal
