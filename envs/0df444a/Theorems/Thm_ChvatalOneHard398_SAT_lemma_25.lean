-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_lemma_25
-- name    : ChvatalOneHard398.SAT.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:35.716095+00:00
-- url     : https://prove2.me/theorems/699f28da-097f-477b-8f5e-f0201f8d9370
-- title:
--   Lemma 25 — making a rational lattice integral
-- statement:
--   Uniformly in positive dimension $n$, a deterministic polynomial-time algorithm takes a rational basis $B$ of $L$, rational $t$, and rational $\nu>\sqrt n$, and returns a basis $B'$ of the same lattice, $v_0\in L$, rational $S>0$, nonsingular integer $M_0$, and integer $t'$, of polynomial encoding size, with
--
--   $$\nu(3/2)^n\le S\lambda_1(L)\le\nu(3/2)^n2^{(n+1)/2},\qquad\lambda_1(M_0\mathbb Z^n)\ge(1-\sqrt n/\nu)S\lambda_1(L).$$
--
--   For every closest $v^*\in L$ and integer $y^*$ with $v^*=v_0+B'y^*$, the integer vector $e^*=t'-M_0y^*$ satisfies
--
--   $$\|e^*\|_\infty\le(1+1/\nu)S\operatorname{dist}(t,L)+\tfrac12+\tfrac12(3/2)^n.$$
--
--   This provides the complete rounding specification. Polynomial encoding size follows from the fixed polynomial TM bound for writing all output coordinates.
--
--   Differences from the source:
--   - encoding: real coordinate vectors, integer points, and lattice notation → Fin-indexed real coordinates, explicit integer-point predicates, and Euclidean integer column spans; reason: these represent the same vectors and full-rank lattices; norms on lattices are Euclidean
--   - encoding: deterministic polynomial time in structured bit size → TM2 polynomial time with fixed, dimension-prefixed, length-framed binary encodings; reason: these encodings are injective and have length linear in the corresponding bit size
--   - encoding: the shortest-nonzero-vector setting of positive-dimensional lattices → n>0 for correct rounding outputs, with a total polynomial algorithm on every raw input; reason: the displayed lower bound uses λ₁, which has no shortest nonzero vector in dimension zero
--   - encoding: the infinity norm of the integer error e* → one absolute-value bound per coordinate of t′−M₀y*; reason: this is exactly the finite-dimensional sup norm, and integrality is carried by the integer expression
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.26, Lemma 25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Rounding

namespace ChvatalOneHard398.SAT

theorem lemma_25 :
    ∃ f : RoundInput → RoundData, PolyTime encRoundInput encRoundData f ∧
      ∀ x, 0 < x.1.n → x.1.basis.det ≠ 0 → Real.sqrt x.1.n < (x.2 : ℝ) →
        RoundCorrect x (f x) := by sorry

end ChvatalOneHard398.SAT
