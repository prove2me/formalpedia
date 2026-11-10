-- Prove2me | Theorems.Thm_EzeunalaJiangKS_Signing_theorem_1_1
-- name    : EzeunalaJiangKS.Signing.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:03:03.726844+00:00
-- url     : https://prove2.me/theorems/094d09ac-2694-4b41-850d-020097a4b564
-- title:
--   Theorem 1.1 — Algorithmic rank-one matrix discrepancy
-- statement:
--   There is one deterministic finite-alphabet Turing machine and natural constants $C\ge1,k$, chosen before every input, that signs every list of rational complex Hermitian matrices $H_1,\ldots,H_N\in\mathbb C^{d\times d}$ of rank at most one. On its canonical binary input word $w$ it halts within $C(|w|+1)^k$ actual transitions, with $N$ sign bits on the tape, decoding to $s_i\in\{-1,1\}$ and satisfying
--   $$\left\|\sum_{i=1}^N s_iH_i\right\|_{2\to2}\le13\sqrt{\left\|\sum_{i=1}^N H_i^2\right\|_{2\to2}}.$$
--   There is no PSD, nonzero, real-only, normalization, bounded-denominator, or positive-dimension restriction. Matrix squares are products. Empty lists, zero dimension, zero matrices, and negative rank-one eigenvalues remain allowed.
--
--   This is the source's bit-algorithm claim, not just sign existence. The program has no real-operation or optimization oracle. The output predicate only reads the actual tape bits.
--
--   Differences from the source:
--   - reading: deterministic polynomial time on rational inputs, with polynomial bit complexity in the rationality footnote → one ordinary finite Post-Turing machine with a uniform polynomial clock in input bit length; reason: the explicit bit-complexity footnote supports this computational reading; uniform program and clock constants precede every input
--   - encoding: rational complex matrix list and output signs → canonical gamma-style dimensions, signed reduced numerator and positive denominator, matrix markers and final zero; final-head tape bits 0 maps to -1 and 1 maps to +1; reason: this is a faithful binary presentation of every source instance; each matrix has a marker even at dimension zero and the output is actual tape content
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), Theorem 1.1, printed p. 1 (PDF p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_BitMachine

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Theorem 1.1, printed p.1 / PDF p.2. One finite Post-Turing machine, polynomial bit time. -/
theorem theorem_1_1 :
  ∃ (q : ℕ) (M : BitProgram q) (C k : ℕ), polynomialSigning q M C k := by sorry

end EzeunalaJiangKS.Signing
