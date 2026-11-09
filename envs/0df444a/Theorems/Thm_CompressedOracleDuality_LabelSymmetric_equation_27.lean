-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_equation_27
-- name    : CompressedOracleDuality.LabelSymmetric.equation_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:37.926187+00:00
-- url     : https://prove2.me/theorems/39613ae6-7b37-448e-9312-9ff070797616
-- title:
--   Equation (27) — both information and memory inequalities
-- statement:
--   Let $G$ be a positive semidefinite trace-one database matrix and let $S$ be a natural number such that $\operatorname{rank}G\le2^S$. The joint law $p(\widetilde D,D)=|(\sqrt G)_{\widetilde D,D}|^2$ satisfies
--   $$I(D;\widetilde D)\le\log_2\operatorname{rank}G\le S.$$
--   This relates classical database correlation to the memory dimension; both inequalities are retained.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - generalization: G is the Gram matrix of a joint adversary–oracle state → any positive semidefinite trace-one matrix on databases; reason: every such matrix has a finite coefficient factorization, so it represents exactly such a state without assuming a query history
--   - generalization: standing N ≥ 64 → all n ≥ 0 in this algebraic or information statement; reason: the finite matrix identity and measurement bound do not use the lower bound on N and include every source instance
--   - generalization: standing S ≥ log₂ N → any natural S satisfying rank(G) ≤ 2^S; reason: the rank-to-log inequality holds for every nonnegative integer S and includes the full standing range
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 16, (27)

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- (27), p.16: both inequalities, with the memory/rank hypothesis for the second. -/
theorem equation_27 {n S : ℕ} (G : DBMatrix n) (hG : G.PosSemidef)
    (htr : G.trace = 1) (hrank : G.rank ≤ 2 ^ S) :
    databaseInformation G ≤ Real.logb 2 G.rank ∧ Real.logb 2 G.rank ≤ S := by sorry

end CompressedOracleDuality.LabelSymmetric
