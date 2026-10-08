-- Prove2me | Theorems.Thm_BellmanDP_Markovian_discrete_growth_asymptotics
-- name    : BellmanDP.Markovian.discrete_growth_asymptotics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T21:57:30.192459+00:00
-- url     : https://prove2.me/theorems/c9e275cb-5e71-41c4-9761-5c61329e2103
-- title:
--   Chapter XI, Theorem 3 (corrected) — $x_i(n)\sim a\,y_i\lambda^n$ for the recurrence $x(n+1)=\max_q A(q)x(n)$
-- statement:
--   Assume the setting and conditions (10.3) of Theorem 2 (with $N \ge 1$), and assume in addition that the Perron root $\varphi(q)$ attains its maximum over $S$ at exactly one joint parameter $q^*$. Let $c \in \mathbb R^N$ with $c_i \ge 0$ for all $i$ and $c \ne 0$, and define
--   $$x_i(0) = c_i, \qquad x_i(n+1) = \max_q \sum_{j=1}^N a_{ij}(q)\, x_j(n), \qquad i = 1,\dots,N,\ n \ge 0 .$$
--   Let $\lambda > 0$ and $y$ with $y_i > 0$ be the solution of the homogeneous system of Theorem 2. Then there is a constant $a = a(c_1,\dots,c_N) > 0$ with
--   $$x_i(n) \sim a\, y_i\, \lambda^n \qquad (n \to \infty),$$
--   that is, $x_i(n)/\lambda^n \to a\, y_i$ for every $i$.
--
--   The theorem describes the long-run growth of the optimally controlled discrete process: it grows geometrically at the maximal Perron root, in the direction of the positive eigenvector of Theorem 2.
--
--   **Formalization Note** The book prints "a unique $q$ for which the maximum value of $q$ is assumed"; a parameter has no maximum value, and the proof works with "$q^*$ \dots the value of $q$ for which $\lambda = \varphi(q^*)$", so the hypothesis is read as uniqueness of the maximizer of $\varphi$ (condition (10.3c)). The book takes $c_i \ge 0$ and then "$c_i > 0$, without loss of generality"; for $c = 0$ the sequence is identically zero and $x_i(n) \sim a y_i \lambda^n$ with $a > 0$ fails, so $c \ne 0$ is assumed. Asymptotic equivalence with a positive limit is stated as convergence of the ratio.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter XI, Theorem 3, p. 330 (with Eqs. (10.1), (10.3), pp. 328-329; proof pp. 331-332)

import Mathlib
import Definitions.Def_BellmanDP_Markovian_Discrete

namespace BellmanDP.Markovian

open Filter Topology

/-- Bellman, *Dynamic Programming*, Ch. XI, Theorem 3, p. 330 (corrected: the printed "unique
q for which the maximum value of q is assumed" is read as the maximum of the Perron root `φ(q)`,
as in (10.3c) and the proof). Under (10.3a)–(c), if `φ` has a unique maximizer on `S` and the
initial vector `c ≥ 0` is not zero, then for the positive solution `(λ, y)` of (10.2) the sequence
(10.1) satisfies `x_i(n) ~ a y_i λⁿ` with a constant `a = a(c) > 0`, i.e.
`x_i(n) / λⁿ → a y_i` for every `i`. -/
theorem discrete_growth_asymptotics {N : ℕ} (hN : 0 < N) {Q : Fin N → Type*}
    (a : (i : Fin N) → Q i → Fin N → ℝ) (S : (i : Fin N) → Set (Q i)) (m : ℝ)
    (h : MarkovHyp a S m)
    (huniq : ∃! qs, qs ∈ Set.pi Set.univ S ∧ ∀ q ∈ Set.pi Set.univ S,
      perronRoot (matOf a q) ≤ perronRoot (matOf a qs))
    (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i) (hc0 : c ≠ 0)
    (lam : ℝ) (y : Fin N → ℝ) (hlam : 0 < lam) (hy : ∀ i, 0 < y i)
    (hey : IsMaxEigenpair a S lam y) :
    ∃ α : ℝ, 0 < α ∧ ∀ i : Fin N,
      Tendsto (fun n : ℕ => maxIter a S c n i / lam ^ n) atTop (𝓝 (α * y i)) := by sorry

end BellmanDP.Markovian
