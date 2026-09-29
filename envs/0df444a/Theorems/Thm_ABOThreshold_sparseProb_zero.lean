-- Prove2me | Theorems.Thm_ABOThreshold_sparseProb_zero
-- name    : ABOThreshold.sparseProb_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:40:41.933993+00:00
-- url     : https://prove2.me/theorems/f2dd2522-9ecb-47e8-bdab-d65bf97fc38e
-- title:
--   Base case: a $0$-rectangle is sparse with probability $1-\eta$
-- statement:
--   A $0$-rectangle is a single location, and by Definition 18 a $(0,k)$-sparse set of faults there is the empty set: the pattern is sparse exactly when no fault occurred at that location.
--
--   The assertion is the resulting identity for the sparseness probability at level $0$,
--
--   $$P(0) \;=\; 1-\eta,$$
--
--   for every error rate $\eta$. It is the base case of the induction of Lemma 10, and it also pins down the convention that the weight of a clean location is $1-\eta$.
-- source:
--   Dorit Aharonov and Michael Ben-Or, Fault-Tolerant Quantum Computation With Constant Error Rate, arXiv:quant-ph/9906129v1, https://arxiv.org/abs/quant-ph/9906129, p. 52, proof of Lemma 10 (base case $r=0$); Definition 18, p. 50

import Definitions.Def_ABOThreshold_model

namespace ABOThreshold

theorem sparseProb_zero (A k : ℕ) (η : ℝ) : sparseProb A k η 0 = 1 - η := by sorry

end ABOThreshold
