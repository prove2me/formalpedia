-- Prove2me | Theorems.Thm_AggNash_Existence_lemma_5_1
-- name    : AggNash.Existence.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:20.693966+00:00
-- url     : https://prove2.me/theorems/1fe7a5f4-2c16-4932-ac43-d1c302a8d494
-- title:
--   Lemma 5.1, p. 15 — the argmin map of a ρ continuous in x, jointly l.s.c., convex in y, has a fixed point
-- statement:
--   Let $R$ be a nonempty, convex, compact subset of a finite-dimensional real normed space $V$. Let $\rho:R\times R\to\mathbb R$ satisfy:
--
--   1. for each fixed $y\in R$, $x\mapsto\rho(x,y)$ is continuous on $R$;
--   2. $(x,y)\mapsto\rho(x,y)$ is lower semicontinuous on $R\times R$;
--   3. for each fixed $x\in R$, $y\mapsto\rho(x,y)$ is convex on $R$.
--
--   Then the set-valued map $\zeta(x)=\operatorname{arg\,min}_{z\in R}\rho(x,z)$ has a fixed point: there is $x\in R$ with
--
--   $$
--   \rho(x,x)\le\rho(x,z)\qquad\text{for all } z\in R.
--   $$
--
--   This is the fixed-point step behind the existence of pure Nash equilibria in lower semicontinuous convex games (Theorem 5.3), where $\rho(x,y)=\sum_i f_i(y_i,x_{-i})$.
--
--   **Formalization Note** The paper states the lemma in $\mathbb R^n$; the statement here is for an arbitrary finite-dimensional real normed space, so that it applies directly to spaces of profiles. $\rho$ is a function on $V\times V$ of which only the values on $R\times R$ matter.
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, p. 15, Lemma 5.1

import Mathlib

namespace AggNash.Existence

/-- Lemma 5.1 (p. 15). Let `R` be a nonempty convex compact set in a finite-dimensional real
normed space. If `ρ : R × R → ℝ` is continuous in `x` on `R` for every fixed `y ∈ R`, lower
semicontinuous in `(x, y)` on `R × R`, and convex in `y` on `R` for every fixed `x ∈ R`, then the
argmin map `x ↦ argmin_{z ∈ R} ρ(x, z)` has a fixed point. -/
theorem lemma_5_1 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (R : Set V) (hne : R.Nonempty) (hconv : Convex ℝ R) (hcpt : IsCompact R)
    (ρ : V → V → ℝ)
    (hcont : ∀ y ∈ R, ContinuousOn (fun x => ρ x y) R)
    (hlsc : LowerSemicontinuousOn (fun p : V × V => ρ p.1 p.2) (R ×ˢ R))
    (hcvx : ∀ x ∈ R, ConvexOn ℝ R (ρ x)) :
    ∃ x ∈ R, ∀ z ∈ R, ρ x x ≤ ρ x z := by sorry

end AggNash.Existence
