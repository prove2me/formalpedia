-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_equation_67
-- name    : CompressedOracleDuality.LabelSymmetric.equation_67
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:09.19621+00:00
-- url     : https://prove2.me/theorems/70771b7f-ced6-45f6-87a0-18dac84da755
-- title:
--   Equation (67) — matched labels and mutual information
-- statement:
--   Let $N=2^n\ge64$ and let $t\in\mathbb N$ satisfy $t^2\le N$. Let $G$ be an arbitrary positive semidefinite trace-one, valid, label-symmetric matrix on databases, whose entries vanish when either database has size greater than $t$. Write $C=C(G)$, let $p(\widetilde D,D)=|(\sqrt G)_{\widetilde D,D}|^2$, and define $C^+$ and $C^-$ as the matched and unmatched label expectations restricted to collision-free $D$. The database $\widetilde D$ need not be collision-free.
--
--   If $t\ge1$, then
--   $$\log_2(N/t)\,C^+-C\le I(D;\widetilde D)\le\log_2\operatorname{rank}G.$$
--   The two-sided estimate connects the number of matched labels to the finite information budget.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - encoding: proof treats t=0 separately before using log(N/t) → 1 ≤ t for this displayed inequality; reason: the ratio is used only in the positive-t part of the proof; no case of Lemma 4.4 is dropped
--   - encoding: real 0 ≤ t ≤ √N → natural t with t² ≤ 2^n; reason: t bounds the integer |D| and is a query count; for real t, applying the Lean statement at ⌊t⌋ gives the bound at t
--   - encoding: trace-one Gram matrix → positive semidefinite matrix with trace 1; reason: G = A†A is positive semidefinite and every such matrix is the Gram matrix of its own square root
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 24, (67), under Lemma 4.4 hypotheses pp. 22–23

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- (67), p.24: matched-label information bound, for t ≥ 1. -/
theorem equation_67 {n t : ℕ} (G : DBMatrix n) (hn : 6 ≤ n)
    (ht : t ^ 2 ≤ 2 ^ n) (hG : G.PosSemidef) (htr : G.trace = 1)
    (hvalid : ValidMatrix G) (hsym : MatrixLabelSymmetric G) (hsupp : SupportedAt G t) (htpos : 1 ≤ t) :
    Real.logb 2 ((2 : ℝ) ^ n / t) * matchedCount G - capacity G ≤ databaseInformation G ∧
    databaseInformation G ≤ Real.logb 2 G.rank := by sorry

end CompressedOracleDuality.LabelSymmetric
