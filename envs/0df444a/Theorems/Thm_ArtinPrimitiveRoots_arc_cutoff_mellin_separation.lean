-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_arc_cutoff_mellin_separation
-- name    : ArtinPrimitiveRoots.arc_cutoff_mellin_separation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T19:59:41.157284+00:00
-- url     : https://prove2.me/theorems/736fcccb-96b1-48c9-bba0-f3d507ae10ee
-- title:
--   The separation (5.15)–(5.16) — ψ(X(w − w′)) e(λX(w − w′)) as a Fourier integral in log w and log w′ with an integrable kernel of size ≪ (1 + |λ|)⁴
-- statement:
--   There is $K > 0$ such that for every $X \ge 10e^6$ and every real $\lambda$ there is a continuous $F : \mathbb R^2 \to \mathbb C$ with
--
--   $$|F(q_1, q_2)| \le \frac{K(1 + |\lambda|)^4}{(1 + q_1^2)(1 + q_2^2)}$$
--
--   and, for all $w, w' \in [1, 16]$,
--
--   $$\psi(X(w - w'))\,e(\lambda X(w - w')) = \int_{\mathbb R^2}F(q)\,e\bigl(q_1X\log w + (q_2 - Xq_1)\log w'\bigr)\,dq,$$
--
--   where $\psi$ is the arc cutoff (`arcCutoff`, bundle `Def_ArtinMarkedSquare`) and $e(u) = \exp(2\pi iu)$.
--
--   A step in the proof of Lemma 10.2's major-term bound `major_square_bound`: the separation of variables (5.15)–(5.16) in the proof of [21, Proposition 5.1] (OpenAI, *The Poisson–Dirichlet law for prime predecessors*), written here as a two-dimensional Fourier integral in logarithmic coordinates.
--
--   OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 37: “$\psi_\lambda(X(w - w')) = \iint F_\lambda(t/X, s')\,w^{it}(w')^{i(s'-t)}\,dt\,ds'$ (5.15)” and “$|F_\lambda(v, s')| \ll_j (1 + |v|/L^{B_0})^{-j}(1 + |s'|/L^{B_0})^{-j}$. (5.16)”
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 37, proof of Proposition 5.1, the separation (5.15)–(5.16) of the arc cutoff

import Mathlib
import Definitions.Def_ArtinMarkedSquare

namespace ArtinPrimitiveRoots

open Real

theorem arc_cutoff_mellin_separation : ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 10 * Real.exp 6 ≤ X → ∀ lam : ℝ,
    ∃ F : ℝ × ℝ → ℂ, Continuous F ∧
      (∀ q : ℝ × ℝ, ‖F q‖ ≤ K * (1 + |lam|) ^ 4 / ((1 + q.1 ^ 2) * (1 + q.2 ^ 2))) ∧
      ∀ w w' : ℝ, 1 ≤ w → w ≤ 16 → 1 ≤ w' → w' ≤ 16 →
        (arcCutoff (X * (w - w')) : ℂ) *
            Complex.exp (2 * π * Complex.I * lam * ((X * (w - w') : ℝ) : ℂ)) =
          ∫ q : ℝ × ℝ, F q * Complex.exp (2 * π * Complex.I *
            (q.1 * X * Real.log w + (q.2 - X * q.1) * Real.log w')) := by
  sorry

end ArtinPrimitiveRoots
