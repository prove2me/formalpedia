-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_Supplement_theorem_5_3
-- name    : CompressedOracleDuality.LabelSymmetric.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:10:30.560005+00:00
-- url     : https://prove2.me/theorems/e01784ca-49d3-40cb-9646-51d208d610ad
-- title:
--   Theorem 5.3 — classical collision time-space tradeoff
-- statement:
--   There is one universal real constant $c>0$ such that the following holds for every $n\ge6$, every natural space and query bounds $S\ge n$ and $T$, and every deterministic label-symmetric collision branching program $B$ with at most $2^S$ vertices in each internal layer. Terminal output leaves have no width bound, and transitions may merge. Set $N=2^n$. If the actual output reports an ordered triple $(x_1,x_2,y)$ with $x_1<x_2$ and $H(x_1)=H(x_2)=y$ with probability at least $2/3$, averaged uniformly over all $N^N$ functions $H$, then
--   $$cN\log_2 N\le TS.$$
--   The same constant works for every program, output map, size, time bound, and space bound. All query counts are covered, without a restriction such as $T<N/2$ or $T\le\sqrt N$. Neither matched-label nor progress estimates are hypotheses. This is the independent classical companion theorem; it is not used in the proof of the mission's quantum goal.
--
--   Differences from the source:
--   - encoding: one carrier [N] for inputs and labels → published Fin (2^n) inputs and n-bit labels, identified by the fixed most-significant-bit-first bijection e; reason: e transports every oracle and label permutation bijectively; input ordering is the published strict order
--   - encoding: a singleton start layer, exactly 2^S internal vertices, and arbitrarily many terminal leaves → finite layer types with a Unique initial layer and at most 2^S vertices only for 1 <= t < T; reason: padding unreachable internal vertices recovers the printed width without altering executions, symmetry, or success; T=0 retains one fixed output
--   - encoding: TS = Omega(N log N), with the standing N >= 64 and S >= log_2 N → a single existential c>0 before n,S,T,B, with c*2^n*n <= T*S for every n>=6 and S>=n; reason: this expands the asymptotic bound uniformly over all algorithms and includes every standing size regime; log_2(2^n)=n
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94; source.pdf SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, Theorem 5.3, (79), p.27; proof p.30; standing assumptions p.11

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Supplement_ClassicalModel

namespace CompressedOracleDuality.LabelSymmetric.Supplement

/-- Theorem 5.3, (79), p.27: one constant before every size, space, time, and program.
No matched-label or progress bound is a hypothesis of this theorem. -/
theorem theorem_5_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n S T : ℕ) (B : ClassicalProgram n T),
      6 ≤ n → n ≤ S → B.SpaceBound S → ClassicalLabelSymmetric B →
      (2 : ℝ) / 3 ≤ classicalSuccess B →
      c * (2 : ℝ) ^ n * (n : ℝ) ≤ (T : ℝ) * (S : ℝ) := by sorry

end CompressedOracleDuality.LabelSymmetric.Supplement
