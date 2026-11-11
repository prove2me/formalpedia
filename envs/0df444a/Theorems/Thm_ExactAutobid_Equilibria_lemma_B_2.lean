-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_lemma_B_2
-- name    : ExactAutobid.Equilibria.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:49.795674+00:00
-- url     : https://prove2.me/theorems/ae3a0c72-fb2c-4ebe-aa9f-04484357908a
-- title:
--   Lemma B.2 — decreasing capped affine gates implement every fixed signed clipped affine expression
-- statement:
--   Consider the gates
--   $$y = \min\Big\{1,\; c - \sum_{j=1}^{k} a_j x_j\Big\},\qquad k \in \{0,1,2\},\; a_j \ge 0,\; c \ge \sum_{j=1}^k a_j,$$
--   with rational constants and inputs in $[0,1]$. For every $n$ and every rational signed affine expression $f(x) = c + \sum_{j<n} a_j x_j$, these gates implement $x \mapsto \mathrm{clip}_{[0,1]}(f(x))$ on $[0,1]^n$ by a fixed-size subcircuit in which all intermediate values lie in $[0,1]$ and every input assignment uniquely determines the internal values.
--
--   This is the affine half of the arithmetic used by every reduction: each auction gadget realizes one such decreasing capped gate.
--
--   Differences from the source:
--   - encoding: these gates implement any fixed rational signed affine expression followed by clipping → ImplementsUniquelyIn01 decCapGates (unitCube n) (clip01 ∘ f) for all n, c, a: one finite subcircuit, every input extends, internal values unique and in [0,1], output = clip01(f(x)); reason: the implementation notion of the mission's Circuits definition
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 58 (PDF 60), Lemma B.2

import Mathlib
import Definitions.Def_ExactAutobid_Equilibria_Circuits

namespace ExactAutobid.Equilibria

/-- **Lemma B.2 (Constructing Clipped Affine Expressions).** The gates
`y = min{1, c − Σ_{j=1}^k a_j x_j}` (`k ≤ 2`, `a_j ≥ 0`, `c ≥ Σ a_j`, rational constants, inputs in
`[0, 1]`) implement every fixed rational signed affine expression followed by clipping to `[0, 1]`,
by a fixed-size subcircuit whose intermediate values lie in `[0, 1]` and are uniquely determined by
the input. -/
theorem lemma_B_2 (n : ℕ) (c : ℚ) (a : Fin n → ℚ) :
    ImplementsUniquelyIn01 decCapGates (unitCube n)
      (fun x => clip01 ((c : ℝ) + ∑ j, (a j : ℝ) * x j)) := by sorry

end ExactAutobid.Equilibria
