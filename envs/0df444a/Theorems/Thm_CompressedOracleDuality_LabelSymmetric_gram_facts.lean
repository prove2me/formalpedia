-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_gram_facts
-- name    : CompressedOracleDuality.LabelSymmetric.gram_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:32.485644+00:00
-- url     : https://prove2.me/theorems/957e96f4-bc4e-407a-ad32-01f8e0756bbe
-- title:
--   §2.3 — trace, rank, support and validity of the run Gram matrix
-- statement:
--   Let $N=2^n\ge64$. Let $A$ be a $T$-query unitary algorithm with a finite workspace $W$ and total memory dimension $N^2|W|\le2^S$. At every time $t\in\{0,\ldots,T\}$, let $B_t$ be the coefficient matrix of its compressed run and $G_t=B_t^\dagger B_t$. Then
--   $$G_t\succeq0,\quad\operatorname{Tr}G_t=1,\quad\operatorname{rank}G_t\le2^S.$$
--   Moreover, $G_t$ is supported on databases of size at most $t$ in both indices, and its image is in the valid compressed-oracle subspace. These facts make the abstract Gram-matrix results applicable to every query time.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - generalization: initial memory is |0^S⟩ → any oracle-independent unit start vector; reason: a fixed change of initial vector is absorbed into V₀ without queries or extra memory
--   - generalization: memory dimension is exactly 2^S → finite W with N² card(W) ≤ 2^S; reason: the source is included by taking W to be the remaining S−2n qubits; smaller spaces embed in the stated bound
--   - encoding: CStO decompresses and recompresses the queried cell → the published compressedOracle conjugates lookup by compression on all cells; reason: the involutions on unqueried cells commute with lookup and cancel in pairs
--   - encoding: standing S ≥ log N → no separate binder; reason: N² card(W) ≤ 2^S with W nonempty (a unit start vector exists only then) already gives S ≥ 2n
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 14, §2.3 following (20)

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- §2.3, p.14: all the Gram facts, for every intermediate query time. -/
theorem gram_facts {n S T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1))
    (hn : 6 ≤ n) (hmem : 2 ^ n * 2 ^ n * Fintype.card W ≤ 2 ^ S) :
    (gramAt A t).PosSemidef ∧ (gramAt A t).trace = 1 ∧
    (gramAt A t).rank ≤ 2 ^ S ∧ SupportedAt (gramAt A t) t.val ∧ ValidMatrix (gramAt A t) := by sorry

end CompressedOracleDuality.LabelSymmetric
