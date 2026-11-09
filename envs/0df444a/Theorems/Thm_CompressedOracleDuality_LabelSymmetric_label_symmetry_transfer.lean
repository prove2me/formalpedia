-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_label_symmetry_transfer
-- name    : CompressedOracleDuality.LabelSymmetric.label_symmetry_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:40.954348+00:00
-- url     : https://prove2.me/theorems/f767099f-ae0c-43fd-8176-8bd02c6b2ae5
-- title:
--   Definition 4.1 / §4.2 — symmetry equivalence and square-root transfer
-- statement:
--   Let $A$ be a unitary query algorithm on $N=2^n$ inputs and labels, with finite workspace. Its overlaps are invariant under all label permutations at every query time if and only if every compressed-run Gram matrix is invariant under simultaneous relabeling of both database indices:
--   $$A\text{ is label-symmetric}\iff\forall t\le T,\sigma,D_1,D_2,\quad(G_t)_{\sigma\circ D_1,\sigma\circ D_2}=(G_t)_{D_1,D_2}.$$
--   For a label-symmetric $A$, the square root $\sqrt{G_t}$ is likewise label-symmetric for every $t$. Relabeling fixes $\bot$. This transfers the algorithm's overlap condition, in both directions, to the matrices used by the capacity argument.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - generalization: initial memory is |0^S⟩ → any oracle-independent unit start vector; reason: a fixed change of initial vector is absorbed into V₀ without queries or extra memory
--   - encoding: CStO decompresses and recompresses the queried cell → the published compressedOracle conjugates lookup by compression on all cells; reason: the involutions on unqueried cells commute with lookup and cancel in pairs
--   - generalization: standing N ≥ 64 → all n ≥ 0 in this algebraic or information statement; reason: the finite matrix identity and measurement bound do not use the lower bound on N and include every source instance
--   - generalization: workspace consists of a finite number of qubits → any finite workspace basis W; reason: a finite workspace embeds in sufficiently many qubits with the same oracle action, overlaps and output law; this item asserts no numerical space bound
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 20, Definition 4.1 equivalence; p. 22, §4.2 opening paragraph

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- Definition 4.1 equivalence (p.20) and square-root symmetry (p.22). -/
theorem label_symmetry_transfer {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) :
    (IsLabelSymmetric A ↔ ∀ t : Fin (T + 1), MatrixLabelSymmetric (gramAt A t)) ∧
    (IsLabelSymmetric A → ∀ t : Fin (T + 1), MatrixLabelSymmetric (sqrtGram (gramAt A t))) := by sorry

end CompressedOracleDuality.LabelSymmetric
