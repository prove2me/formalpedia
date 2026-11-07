-- Prove2me | Theorems.Thm_FixpReciprocal_square_slReduces_reciprocal
-- name    : FixpReciprocal.square_slReduces_reciprocal
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:50:55.564464+00:00
-- url     : https://prove2.me/theorems/1aa7f1b7-0f4d-4464-b253-b3a4e32d0673
-- title:
--   Theorem 4.2 (proof, hardness) — the replacement is an SL-reduction
-- statement:
--   For every rational $\tau>0$, the problem of Lemma 3.4 admits an SL-reduction to the problem with the gates of (1), both over all circuits and over the circuits with a nonconstant gate.
--
--   The reduction maps $\mathcal C$ to $\mathcal C'$ in polynomial time, and the recovery is restriction to the original coordinates, $x_i=y_i$. Combined with Lemma 3.4 this gives the hardness half of the main theorem.
--
--   Differences from the source:
--
--   - reading: polynomial time → Mathlib's Turing.TM2ComputableInPolyTime over fixed binary encodings in the alphabet Sym; reason: the paper names no machine model; §3, p.10 measures input size by bit length
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), proof of Theorem 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FixpReciprocal_SLReduces
import Definitions.Def_FixpReciprocal_reciprocalProblem
import Definitions.Def_FixpReciprocal_squareProblem

namespace FixpReciprocal

/-- **Proof of Theorem 4.2, the SL-reduction.** "The new circuit has at most `7N` gates and can be constructed in
polynomial time. Restriction to the original coordinates is an SL-reduction."

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), proof of Theorem 4.2, p.12.

**Formalization Note.** Both targets: every `replaceSq` output has a nonconstant gate. -/
theorem square_slReduces_reciprocal (τ : ℚ) (hτ : 0 < τ) :
    SLReduces squareProblem (reciprocalProblem τ) ∧
    SLReduces squareProblem (reciprocalProblemNC τ) := by sorry

end FixpReciprocal
