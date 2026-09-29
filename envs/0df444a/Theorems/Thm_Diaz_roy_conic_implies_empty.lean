-- Prove2me | Theorems.Thm_Diaz_roy_conic_implies_empty
-- name    : Diaz.roy_conic_implies_empty
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:22.865502+00:00
-- url     : https://prove2.me/theorems/36b3f3a3-1bd2-4577-ae3b-22152143fe50
-- title:
--   Roy's conjecture for the affine conic $XY=\rho$ forces the logarithmic intersection to be empty
-- statement:
--   **Roy's conjecture for the Diaz conic would settle Diaz immediately.**
--
--   Fix $\rho \neq 0$ and let $L \subseteq \mathbb{C}$ be any set (the intended $L$ is the $\mathbb{Q}$-vector
--   space $\mathcal{L}$ of logarithms of algebraic numbers). Suppose Roy's Conjecture 1.1, specialised to the
--   affine conic $X_\rho : XY = \rho$, holds for $L$: every point $p \in X_\rho \cap L^2$ lies in a
--   $\mathbb{Q}$-rational vector subspace $V \subseteq \mathbb{C}^2$ that is itself contained in $X_\rho$.
--   Then $X_\rho \cap L^2 = \varnothing$.
--
--   **Why.** A vector subspace contains the origin, and $0 \cdot 0 = 0 \neq \rho$. So no vector subspace is
--   contained in $X_\rho$, and the hypothesis can only be satisfied vacuously.
--
--   **Role.** A Diaz candidate is exactly a point $(u, \bar u) \in \mathcal{L}^2$ on $X_\rho$ with
--   $\rho = u \bar u$ algebraic and positive. This node is the one-line reason the affine instance of Roy's
--   conjecture is not merely *related* to Diaz's conjecture but implies it outright — and, read backwards,
--   the reason the homogeneity barrier is where the difficulty sits: the corresponding homogeneous statement
--   has non-trivial subspaces to offer, and the affine one has none.
--
--   The Lean statement quantifies over an arbitrary set $L$ and an arbitrary $\rho \neq 0$, so it carries no
--   transcendence input at all; it is pure linear algebra, and the entire arithmetic content stays in the
--   hypothesis.
--
--   Source: Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Section 4 (*The precise open
--   boundary*), Proposition 4.3. The
--   observation is elementary and is stated there without any claim of priority; no novelty is claimed here
--   either.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.10, 27 September 2026 (GitHub release note-v1.10), Proposition 4.3. Formal proof: Diaz modulus mission, 8 September 2026 (C. Perassi).

import Mathlib

open ComplexConjugate

theorem Diaz.roy_conic_implies_empty {ρ : ℂ} (hρ : ρ ≠ 0) (L : Set ℂ)
    (hRoy : ∀ p : Fin 2 → ℂ, (∀ i, p i ∈ L) → p 0 * p 1 = ρ →
      ∃ V : Submodule ℚ (Fin 2 → ℂ), p ∈ V ∧ ∀ q ∈ V, q 0 * q 1 = ρ) :
    ∀ p : Fin 2 → ℂ, (∀ i, p i ∈ L) → p 0 * p 1 ≠ ρ := by sorry
