-- Prove2me | Theorems.Thm_FixpReciprocal_reciprocal_mem_FIXP
-- name    : FixpReciprocal.reciprocal_mem_FIXP
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:52:44.903614+00:00
-- url     : https://prove2.me/theorems/4be010de-b09a-4058-bc0c-7f86819e7c20
-- title:
--   Theorem 4.2 (proof, membership) — the problem belongs to FIXP
-- statement:
--   For every rational $\tau>0$, finding a solution of a generalized circuit with the gates of (1) belongs to FIXP, both over all circuits and over the circuits with a nonconstant gate.
--
--   This is the membership half of the main theorem. The instance $([0,1]^N,F_{\mathcal C})$ has the same solution set as $\mathcal C$.
--
--   Differences from the source:
--
--   - reading: polynomial time → Mathlib's Turing.TM2ComputableInPolyTime over fixed binary encodings in the alphabet Sym; reason: the paper names no machine model; §3, p.10 measures input size by bit length
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), proof of Theorem 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_FixpReciprocal_reciprocalProblem

namespace FixpReciprocal

/-- **Proof of Theorem 4.2, membership.** "so `([0, 1]^N, F_C)` is a basic FIXP instance (Definition 3.1) with the
same solution set."

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), proof of Theorem 4.2, p.12.

**Formalization Note.** Both instance sets (Theorem 4.2's goal states completeness for both). -/
theorem reciprocal_mem_FIXP (τ : ℚ) (hτ : 0 < τ) :
    InFIXP (reciprocalProblem τ) ∧ InFIXP (reciprocalProblemNC τ) := by sorry

end FixpReciprocal
