-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_equation_55
-- name    : CompressedOracleDuality.LabelSymmetric.equation_55
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:03:00.219659+00:00
-- url     : https://prove2.me/theorems/73db511f-ce95-42b5-873d-7d70c75e2711
-- title:
--   Equation (55) — collision success from final progress
-- statement:
--   Let $N=2^n\ge64$. Let $A$ be a $T$-query unitary algorithm with finite workspace and a final output map returning a triple $(x_1,x_2,y)$ or failure. Let $p$ be the probability, averaged uniformly over all functions $H$ and over the final measurement, of $x_1<x_2$ and $H(x_1)=H(x_2)=y$. Let $\Delta_T$ be the norm of the colliding-database part of the final compressed state. Then
--   $$p\le\bigl(\Delta_T+\sqrt{2/N}\bigr)^2.$$
--   This relates actual random-oracle success to final compressed progress. It imposes no label symmetry or success threshold.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - generalization: initial memory is |0^S⟩ → any oracle-independent unit start vector; reason: a fixed change of initial vector is absorbed into V₀ without queries or extra memory
--   - encoding: CStO decompresses and recompresses the queried cell → the published compressedOracle conjugates lookup by compression on all cells; reason: the involutions on unqueried cells commute with lookup and cancel in pairs
--   - generalization: workspace consists of a finite number of qubits → any finite workspace basis W; reason: a finite workspace embeds in sufficiently many qubits with the same oracle action, overlaps and output law; this item asserts no numerical space bound
--   - reading: the algorithm outputs a triple, the output step being left unspecified → computational-basis measurement of the whole memory, then an arbitrary map out to a triple or failure; reason: any projective final measurement is absorbed into V_T, which changes no overlap, and none is the source’s failure outcome ⊥
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 21, (55)

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Progress

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- (55), p.21: actual collision success, averaged over the uniformly random oracle. -/
theorem equation_55 {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (out : Memory n W → CollisionOutput n)
    (hn : 6 ≤ n) :
    collisionSuccess A out ≤ (progressAt A (Fin.last T) + Real.sqrt (2 / (2 : ℝ) ^ n)) ^ 2 := by sorry

end CompressedOracleDuality.LabelSymmetric
