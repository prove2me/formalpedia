-- Prove2me | Theorems.Thm_ContiguousCake597_Approximate_Supplement_lemma_12
-- name    : ContiguousCake597.Approximate.Supplement.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:00:19.973212+00:00
-- url     : https://prove2.me/theorems/535585ea-1474-4842-bd8f-c4d08e8480da
-- title:
--   Lemma 12 — PPAD membership of contiguous EF1-outer for goods and for chores
-- statement:
--   Consider $n\ge1$ agents and $m$ items on a path.
--
--   1. For goods with arbitrary nonnegative rational additive valuations, the search problem of computing a contiguous EF$1_{\mathrm{outer}}$ allocation lies in PPAD.
--   2. For chores with arbitrary nonnegative rational additive costs, the search problem of computing a contiguous EF$1_{\mathrm{outer}}$ allocation lies in PPAD.
--
--   Here EF$1_{\mathrm{outer}}$ for goods means: for all $i,j$ one can remove at most one good from $X_j$, leaving a connected or empty set, so that $\nu_i(X_i)\ge\nu_i(X_j\setminus G)$; for chores one removes at most one chore from $X_i$, leaving a connected or empty set, so that $\kappa_i(X_i\setminus G)\le\kappa_i(X_j)$. Membership in PPAD is in the sense of §2.1: the problem is total and reduces to End-of-Line, its answers are verifiable in polynomial time, and every valid input has an answer of polynomial length.
--
--   This supplies the membership half of Theorem 2, since an EF$1_{\mathrm{outer}}$ allocation is EF$c$ and EF$c_{\mathrm{outer}}$ for every $c\ge1$.
--
--   Differences from the source:
--   - encoding: "lies in PPAD" → the published PPAD predicate together with a polynomial-time verifier and short-witness existence; reason: the paper's definition of PPAD in §2.1 includes both requirements, which the published PPAD predicate does not
--   - reading: n agents → n ≥ 1 agents; reason: the paper's standing convention; with no agents and at least one item no allocation exists and the problem would not be total
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 13 (PDF 14), Lemma 12

import Definitions.Def_ContiguousCake597_Approximate_Supplement_Path

namespace ContiguousCake597.Approximate.Supplement

/-- Lemma 12, printed p.13 (PDF 14). Contiguous EF1_outer search lies in PPAD (with the
§2.1 verification and short-witness requirements) for arbitrary nonnegative rational
additive goods valuations and for arbitrary nonnegative rational additive chore costs. -/
theorem lemma_12 :
    PaperPPAD (PathProblem false true (.const 1) false) ∧
    PaperPPAD (PathProblem true true (.const 1) false) := by sorry

end ContiguousCake597.Approximate.Supplement
