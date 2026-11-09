-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_equation_54
-- name    : CompressedOracleDuality.LabelSymmetric.equation_54
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:59.873216+00:00
-- url     : https://prove2.me/theorems/384708cd-75b1-440f-a86b-632fc60769a3
-- title:
--   Equation (54) — collision progress and per-query leakage
-- statement:
--   Let $N=2^n\ge64$, and let $A$ be any $T$-query unitary algorithm with finite workspace. For $0\le t<T$, let $|\psi_t\rangle$ be its normalized compressed state, $G_t$ its Gram matrix, $\Delta_t=\|\Pi_{\ge1}|\psi_t\rangle\|$, and $L_t=\|\Pi_{\ge1}\mathrm{CStO}\,\Pi_{=0}|\psi_t\rangle\|$. Then
--   $$\Delta_{t+1}-\Delta_t\le L_t,\qquad L_t\le\sqrt{16C(G_t)/N}.$$
--   No label symmetry is needed for this progress estimate. The paper imports this bound from Magniez–Zur and Zhandry; both the per-query comparison and the displayed capacity estimate are theorem conclusions here.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - generalization: initial memory is |0^S⟩ → any oracle-independent unit start vector; reason: a fixed change of initial vector is absorbed into V₀ without queries or extra memory
--   - encoding: CStO decompresses and recompresses the queried cell → the published compressedOracle conjugates lookup by compression on all cells; reason: the involutions on unqueried cells commute with lookup and cancel in pairs
--   - generalization: workspace consists of a finite number of qubits → any finite workspace basis W; reason: a finite workspace embeds in sufficiently many qubits with the same oracle action, overlaps and output law; this item asserts no numerical space bound
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 21, per-query sentence and (54), attributed there to [MZ26] and [Zha19]

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Progress

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- §4.1, p.21: per-query progress and (54), without assuming label symmetry. -/
theorem equation_54 {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (hn : 6 ≤ n) (t : Fin T) :
    progressAt A t.succ - progressAt A t.castSucc ≤ queryLeakage A t.castSucc ∧
    queryLeakage A t.castSucc ≤ Real.sqrt (16 * capacity (gramAt A t.castSucc) / (2 : ℝ) ^ n) := by sorry

end CompressedOracleDuality.LabelSymmetric
