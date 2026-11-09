-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_lemma_4_4
-- name    : CompressedOracleDuality.LabelSymmetric.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:25.241285+00:00
-- url     : https://prove2.me/theorems/af7a7e5f-726f-4a56-84cc-5c95ccd162bf
-- title:
--   Lemma 4.4 — quantum collision-free capacity
-- statement:
--   Let $N=2^n\ge64$ and let $t\in\mathbb N$ satisfy $t^2\le N$. Let $G$ be an arbitrary positive semidefinite trace-one, valid, label-symmetric matrix on databases, whose entries vanish when either database has size greater than $t$. Write $C=C(G)$, let $p(\widetilde D,D)=|(\sqrt G)_{\widetilde D,D}|^2$, and define $C^+$ and $C^-$ as the matched and unmatched label expectations restricted to collision-free $D$. The database $\widetilde D$ need not be collision-free.
--
--   Then
--   $$C(G)\le\min\left\{t,\frac{4\log_2\operatorname{rank}G}{\log_2 N}+\frac{8t^2}N\right\}.$$
--   In particular, for every natural space bound $S\ge\log_2N$ with $\operatorname{rank}G\le2^S$,
--   $$C(G)\le\min\{t,12S/\log_2N\}.$$
--   The result applies to every such Gram matrix, independently of whether it is produced by a particular algorithm. It includes the zero-query support case and both clauses with the paper's constants.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - encoding: real 0 ≤ t ≤ √N → natural t with t² ≤ 2^n; reason: t bounds the integer |D| and is a query count; for real t, applying the Lean statement at ⌊t⌋ gives the bound at t
--   - encoding: trace-one Gram matrix → positive semidefinite matrix with trace 1; reason: G = A†A is positive semidefinite and every such matrix is the Gram matrix of its own square root
--   - encoding: standing S ≥ log N in the final clause → explicit quantifier over natural S with n ≤ S; reason: the proof uses it there; log₂ N = n
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 22, Lemma 4.4, (58) and final sentence; proof pp. 23–24

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- Lemma 4.4, p.22, including its final sentence; G is arbitrary, not just a run Gram matrix. -/
theorem lemma_4_4 {n t : ℕ} (G : DBMatrix n) (hn : 6 ≤ n)
    (ht : t ^ 2 ≤ 2 ^ n) (hG : G.PosSemidef) (htr : G.trace = 1)
    (hvalid : ValidMatrix G) (hsym : MatrixLabelSymmetric G) (hsupp : SupportedAt G t) :
    capacity G ≤ min (t : ℝ)
      (4 * Real.logb 2 G.rank / Real.logb 2 ((2 : ℝ) ^ n) + 8 * (t : ℝ) ^ 2 / (2 : ℝ) ^ n) ∧
    (∀ S : ℕ, n ≤ S → G.rank ≤ 2 ^ S →
      capacity G ≤ min (t : ℝ) (12 * (S : ℝ) / Real.logb 2 ((2 : ℝ) ^ n))) := by sorry

end CompressedOracleDuality.LabelSymmetric
