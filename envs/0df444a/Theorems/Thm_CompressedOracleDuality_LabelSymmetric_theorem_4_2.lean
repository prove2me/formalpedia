-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_theorem_4_2
-- name    : CompressedOracleDuality.LabelSymmetric.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:19.619349+00:00
-- url     : https://prove2.me/theorems/ca6d7815-8799-4b5a-b0dd-efa795900d4d
-- title:
--   Theorem 4.2 — quantum collision time–space tradeoff
-- statement:
--   There is a universal real constant $c>0$ such that the following holds for every $n\ge6$, natural query and space bounds $T,S$, and finite workspace basis $W$. Put $N=2^n$. Let $A$ be a unitary $T$-query algorithm with total memory dimension $N^2|W|\le2^S$, using the standard XOR oracle for $H:[N]\to\{0,1\}^n$. Assume $A$ is label-symmetric at every time, in the overlap sense of Definition 4.1. Its final memory measurement is decoded into a triple $(x_1,x_2,y)$ or failure. If the uniform average over all $N^N$ functions $H$ of the probability that $x_1<x_2$ and $H(x_1)=H(x_2)=y$ is at least $2/3$, then
--   $$c\,N\log_2N\le T^2S.$$
--   The same constant works for every size, space bound, query bound, workspace, algorithm, and output map. This is the paper's $T^2S=\Omega(N\log N)$ assertion; it is credited to Magniez–Zur, Theorem 4.19, and Ding–Zhandry supply the alternative proof followed by these milestones.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - generalization: initial memory is |0^S⟩ → any oracle-independent unit start vector; reason: a fixed change of initial vector is absorbed into V₀ without queries or extra memory
--   - generalization: memory dimension is exactly 2^S → finite W with N² card(W) ≤ 2^S; reason: the source is included by taking W to be the remaining S−2n qubits; smaller spaces embed in the stated bound
--   - reading: the algorithm outputs a triple, the output step being left unspecified → computational-basis measurement of the whole memory, then an arbitrary map out to a triple or failure; reason: any projective final measurement is absorbed into V_T, which changes no overlap, and none is the source’s failure outcome ⊥
--   - encoding: standing S ≥ log N → no separate binder; reason: N² card(W) ≤ 2^S with W nonempty (a unit start vector exists only then) already gives S ≥ 2n
--   - encoding: T²S = Ω(N log N) → ∃ c > 0, chosen before all parameters, with c·2^n·n ≤ T²S for every n ≥ 6; reason: the standing N ≥ 64 is the range of the asymptotic claim and log₂ N = n
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 20, Theorem 4.2, (52); proof p. 24, (72)

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Model

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- Theorem 4.2, p.20: c is chosen before all algorithm and size parameters. -/
theorem theorem_4_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n S T : ℕ) (W : Type) [Fintype W] [DecidableEq W]
      (A : QueryAlg (Input n) (Label n) W T) (out : Memory n W → CollisionOutput n),
      6 ≤ n → 2 ^ n * 2 ^ n * Fintype.card W ≤ 2 ^ S →
      IsLabelSymmetric A → (2 : ℝ) / 3 ≤ collisionSuccess A out →
      c * (2 : ℝ) ^ n * (n : ℝ) ≤ (T : ℝ) ^ 2 * (S : ℝ) := by sorry

end CompressedOracleDuality.LabelSymmetric
