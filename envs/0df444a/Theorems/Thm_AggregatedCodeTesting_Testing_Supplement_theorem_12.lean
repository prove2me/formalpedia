-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_Supplement_theorem_12
-- name    : AggregatedCodeTesting.Testing.Supplement.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:31:45.234829+00:00
-- url     : https://prove2.me/theorems/5e1ee3e1-3e27-4612-9dcc-b33b4b8532c8
-- title:
--   Theorem 12 — finite detection-order bound and simultaneous randomized bit algorithm
-- statement:
--   Let $C\le\mathbb F_2^m$ be an informative indecomposable code without identically zero coordinates. Write $r=\dim C^\perp$ and $d=\max_{A\in C^\perp}|A|$. Every nonzero dual character satisfies the exact inequalities
--
--   $$|A|\le t_C(A)\le d\,2^{r-1}.$$
--
--   In particular every such order and their maximum $s^*(C)$ are finite. There exists one randomized algorithm, with a universal positive coefficient $a$ and a universal natural degree $e$, such that for every full-row-rank binary $r\times m$ parity-check matrix defining such a code, and every $0<\delta<1$, its simultaneous success probability is at least $1-\delta$. Its output contains every nonzero dual character, its correct order and the correct maximum. On every random string it halts within
--
--   $$a(1+m+2^r+b)^e,\qquad b=\max\{1,\lceil\log_2(1/\delta)\rceil\}$$
--
--   bit-machine steps. Hence its worst-case bit complexity is polynomial in $m,2^r,\log(1/\delta)$. Uniform independent fair random bits are placed on a separate input tape. Neither code-dependent polynomial constants, an expected-time bound, nor separate per-character success replaces the simultaneous assertion.
--
--   This algorithm computes scalar orders. The larger multivariate witness-table preprocessing needed for exact recovery is covered separately by Theorem 11.
--
--   Differences from the source:
--   - encoding: binary parity-check input and failure tolerance delta → the published binary multi-tape Turing machine with self-delimiting matrix input and precision b=max(1,ceil(log2(1/delta))); reason: every real delta is covered by a binary tolerance within a factor two and b is O(1+log(1/delta))
--   - encoding: simultaneous success probability and polynomial bit operations → one output equality under a uniform T-bit tape and halting on every tape within a code-independent polynomial bound; reason: a T-step machine can inspect at most T tape bits; this preserves worst-case bit complexity and joint success
--   - encoding: finite orders on an informative block and bound d times 2^(r-1) → extended-natural order inequalities with actual dual finrank, and finiteness of sStar concluded; reason: informative implies r at least one, so natural subtraction in r-1 is the ordinary source exponent
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Theorem 12, printed p.11 (PDF p.12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf; pinned PDF SHA256 1f5fce093155b2721073a124d87a3c6947269ff7851c61301dfa6e81232f0b2c

import Definitions.Def_AggregatedCodeTesting_Testing_Supplement_Computation

set_option autoImplicit false
open Finset

namespace AggregatedCodeTesting.Testing.Supplement

/-- Theorem 12, printed p.11 / PDF p.12. Exact finite degree bound and one universal
worst-case bit-time algorithm with simultaneous high-probability output. -/
theorem theorem_12 :
    (∀ m (C : Submodule (ZMod 2) (Word m)), HasNoZeroCoord C →
      IsIndecomposable C → IsInformative C univ →
      (∀ A ∈ dualCode C, A ≠ 0 →
        (weight A : ℕ∞) ≤ detOrder C univ A ∧
        detOrder C univ A ≤ (maxDualWeight C univ *
          2 ^ (Module.finrank (ZMod 2) (orthogonal C) - 1) : ℕ)) ∧
      sStar C ≠ ⊤) ∧
    (∃ algorithm : MetaSearch.Heyting.Machine, ∃ a d : ℕ,
      0 < a ∧ RealizesOrders algorithm a d) := by sorry

end AggregatedCodeTesting.Testing.Supplement
