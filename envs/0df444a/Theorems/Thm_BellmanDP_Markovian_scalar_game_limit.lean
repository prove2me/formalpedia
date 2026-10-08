-- Prove2me | Theorems.Thm_BellmanDP_Markovian_scalar_game_limit
-- name    : BellmanDP.Markovian.scalar_game_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T21:58:06.608399+00:00
-- url     : https://prove2.me/theorems/53d40feb-4179-43a5-9a4b-8525e9689378
-- title:
--   Chapter XI, Theorem 5 — $u(t)\to\max_p\min_q (Ap,q)/(Bp,q)$ for the scalar game equation
-- statement:
--   Let $A$ and $B$ be real $m \times n$ matrices ($m, n \ge 1$), and let $p$, $q$ range over probability vectors in $\mathbb R^n$ and $\mathbb R^m$. Assume $(Bp, q) \ge d > 0$ for all probability vectors $p$ and $q$. Let $u$ be a solution for $t \ge 0$ of the scalar equation
--   $$\frac{du}{dt} = \max_p \min_q \big[(Ap,q) - (Bp,q)\,u\big], \qquad u(0) = c,$$
--   that is, $u$ is continuous on $[0,\infty)$ and $u(t) = c + \int_0^t \max_p\min_q[(Ap,q) - (Bp,q)u(s)]\,ds$. Then
--   $$\lim_{t \to \infty} u(t) = \max_p \min_q \frac{(Ap,q)}{(Bp,q)} = \min_q \max_p \frac{(Ap,q)}{(Bp,q)} .$$
--
--   The theorem recovers the extended min-max theorem for ratios of bilinear forms (Chapter X) as the long-run limit of a differential game.
--
--   **Formalization Note** The book writes the right-hand side also as $\min_q \max_p[\dots]$, which is von Neumann's theorem; the statement uses the max-min form. The limit exists as part of the conclusion, and the equality of the two ratio values is included, as in the book's (3).
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter XI, Theorem 5, p. 333 (with Eq. (13.1), p. 333)

import Mathlib
import Definitions.Def_BellmanDP_Markovian_ScalarGame

namespace BellmanDP.Markovian

open Filter Topology

/-- Bellman, *Dynamic Programming*, Ch. XI, Theorem 5, p. 333. Let `A`, `B` be `m × n` matrices
(`m, n ≥ 1`) with `(Bp, q) ≥ d > 0` for all probability vectors `p`, `q`, and let `u` solve the
scalar equation `du/dt = Max_p Min_q [(Ap, q) − (Bp, q) u]`, `u(0) = c`, for `t ≥ 0` (in integral
form). Then `lim_{t → ∞} u(t) = Max_p Min_q (Ap, q)/(Bp, q) = Min_q Max_p (Ap, q)/(Bp, q)`. -/
theorem scalar_game_limit {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A B : Matrix (Fin m) (Fin n) ℝ) (d : ℝ) (hd : 0 < d)
    (hB : ∀ p ∈ stdSimplex ℝ (Fin n), ∀ q ∈ stdSimplex ℝ (Fin m), d ≤ pairing B p q)
    (c : ℝ) (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Set.Ici 0))
    (hu : ∀ t : ℝ, 0 ≤ t → u t = c + ∫ s in (0 : ℝ)..t, gameRHS A B (u s)) :
    Tendsto u atTop (𝓝 (maxMinRatio A B)) ∧ maxMinRatio A B = minMaxRatio A B := by sorry

end BellmanDP.Markovian
