-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_equation_24
-- name    : CompressedOracleDuality.LabelSymmetric.equation_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:32.623319+00:00
-- url     : https://prove2.me/theorems/8bbc1cf6-09b4-4cd2-bc5b-89cd4d92554a
-- title:
--   Equation (24) — joint-law symmetry, marginals and square-root validity
-- statement:
--   Let $G$ be a positive semidefinite trace-one matrix on compressed databases. Let $p(\widetilde D,D)=|(\sqrt G)_{\widetilde D,D}|^2$. Then
--   $$p(D_1,D_2)=p(D_2,D_1),\quad\sum_{D_2}p(D_1,D_2)=G_{D_1,D_1},\quad\sum_{D_1}p(D_1,D_2)=G_{D_2,D_2}.$$
--   If moreover $G$ has image in the valid subspace, then so does $\sqrt G$. Thus the two database marginals agree with the standard database distribution, and the validity constraint is available on the square root itself.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - generalization: G is the Gram matrix of a joint adversary–oracle state → any positive semidefinite trace-one matrix on databases; reason: every such matrix has a finite coefficient factorization, so it represents exactly such a state without assuming a query history
--   - generalization: standing N ≥ 64 → all n ≥ 0 in this algebraic or information statement; reason: the finite matrix identity and measurement bound do not use the lower bound on N and include every source instance
--   - encoding: diagonal entry G_{D,D} as a probability → real part (G D D).re; reason: diagonal entries of a positive semidefinite matrix are real
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 15, paragraph containing (24)

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- (24), p.15, together with the validity of the square root in the same paragraph. -/
theorem equation_24 {n : ℕ} (G : DBMatrix n) (hG : G.PosSemidef)
    (htr : G.trace = 1) :
    (∀ D₁ D₂, jointLaw G (D₁, D₂) = jointLaw G (D₂, D₁)) ∧
    (∀ D₁, ∑ D₂, jointLaw G (D₁, D₂) = (G D₁ D₁).re) ∧
    (∀ D₂, ∑ D₁, jointLaw G (D₁, D₂) = (G D₂ D₂).re) ∧
    (ValidMatrix G → ValidMatrix (sqrtGram G)) := by sorry

end CompressedOracleDuality.LabelSymmetric
