-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_6_6
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:42:23.7352+00:00
-- url     : https://prove2.me/theorems/9828dd84-0ca7-41c5-980e-af1606113eb0
-- title:
--   Lemma 6.6 — second moment of the reachable set in the sparse regime
-- statement:
--   For every fixed $\gamma>1$ (and fixed $C>0$) there are constants $K>0$, $n_0$ such that for $n\ge\max(n_0,3)$, every source and every $n\le j\le\gamma n$ (with $j\le N$), the number $R$ of vertices reachable from $s$ (including $s$) satisfies
--   $$\mathbb E_jR^2\le K\Bigl(n\log n+\frac{(j-n)^3}{n}\Bigr), \tag{14}$$
--   i.e. $\mathbb E_jR^2=O_\gamma\bigl(n\log n+(j-n)^3/n\bigr)$.
--
--   Differences from the source:
--   - encoding: conditional on the arc set, the present arcs carry independent U[0,C) weights → a U[0,C) weight is drawn independently for each of the n² ordered pairs (including unused diagonal coordinates), and the graph uses the weights of its present arcs (truncated at 0, a null event); reason: the weighted graph has exactly the source's law
--   - encoding: O-bounds whose constants may depend on the displayed fixed parameters (C > 0 fixed) → ∀ C > 0, ∀ fixed parameters, ∃ K > 0, ∃ n₀, ∀ n ≥ n₀ with n ≥ 3, ∀ source, initial count, operation sequence and step; reason: standard meaning of O with the constant chosen before n, m and the update
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 6.6, equation (14), PDF p.10 = printed p.10; proof continues on PDF p.11

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 6.6 (PDF p. 10, proof to p. 11), eq. (14). For every fixed `γ > 1` and
`n ≤ j ≤ γ n`, the number `R` of vertices reachable from `s` satisfies
`𝔼_j R² = O_γ(n log n + (j - n)³/n)`. -/
theorem lemma_6_6 (C : ℝ) (hC : 0 < C) (γ : ℝ) (hγ : 1 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 ≤ n → ∀ (s : Fin n) (j : ℕ),
      n ≤ j → (j : ℝ) ≤ γ * n → j ≤ numPairs n →
        ∫⁻ g, ((reachCount s g : ℝ≥0∞)) ^ 2 ∂(gnm n C j) ≤
          ENNReal.ofReal (K * (n * Real.log n + ((j : ℝ) - n) ^ 3 / n)) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
