-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_equation_71
-- name    : CompressedOracleDuality.LabelSymmetric.equation_71
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:35.969919+00:00
-- url     : https://prove2.me/theorems/0909f1c6-0eb9-46b1-aa3c-eeeb49a17ca3
-- title:
--   Equation (71) — both unmatched-label estimates
-- statement:
--   Let $N=2^n\ge64$ and let $t\in\mathbb N$ satisfy $t^2\le N$. Let $G$ be an arbitrary positive semidefinite trace-one, valid, label-symmetric matrix on databases, whose entries vanish when either database has size greater than $t$. Write $C=C(G)$, let $p(\widetilde D,D)=|(\sqrt G)_{\widetilde D,D}|^2$, and define $C^+$ and $C^-$ as the matched and unmatched label expectations restricted to collision-free $D$. The database $\widetilde D$ need not be collision-free.
--
--   Then
--   $$C^-\le\frac{t(2t-1)}N\le\frac{2t^2}N.$$
--   The formula is in real arithmetic, so $t=0$ gives a zero right-hand side rather than a truncated subtraction artifact. Both inequalities of the source are included.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - encoding: real 0 ≤ t ≤ √N → natural t with t² ≤ 2^n; reason: t bounds the integer |D| and is a query count; for real t, applying the Lean statement at ⌊t⌋ gives the bound at t
--   - encoding: trace-one Gram matrix → positive semidefinite matrix with trace 1; reason: G = A†A is positive semidefinite and every such matrix is the Gram matrix of its own square root
--   - generalization: (71) appears after the proof sets aside t = 0 → t = 0 included; reason: at t = 0 all mass is on the empty database and both sides vanish; every t ≥ 1 is the source claim
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 24, (71), under Lemma 4.4 hypotheses pp. 22–23

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- (71), p.24: subtraction takes place in ℝ, including t = 0. -/
theorem equation_71 {n t : ℕ} (G : DBMatrix n) (hn : 6 ≤ n)
    (ht : t ^ 2 ≤ 2 ^ n) (hG : G.PosSemidef) (htr : G.trace = 1)
    (hvalid : ValidMatrix G) (hsym : MatrixLabelSymmetric G) (hsupp : SupportedAt G t) :
    unmatchedCount G ≤ (t : ℝ) * (2 * (t : ℝ) - 1) / (2 : ℝ) ^ n ∧
    (t : ℝ) * (2 * (t : ℝ) - 1) / (2 : ℝ) ^ n ≤ 2 * (t : ℝ) ^ 2 / (2 : ℝ) ^ n := by sorry

end CompressedOracleDuality.LabelSymmetric
