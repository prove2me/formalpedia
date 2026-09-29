-- Prove2me | Theorems.Thm_Dynamics_periodic_of_shift_smul
-- name    : Dynamics.periodic_of_shift_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:14:30.15503+00:00
-- url     : https://prove2.me/theorems/83c0bb00-4bde-4535-b017-744d31adf4da
-- title:
--   A curve shifted by a group element is periodic with period the order of that element
-- statement:
--   Let a finite group $G$ act on a set $X$, and let $c:\mathbb R\to X$ satisfy
--
--   $$
--   c(s+\lambda)=w\cdot c(s)\qquad\text{for all }s\in\mathbb R
--   $$
--
--   for a fixed $w\in G$ and $\lambda\in\mathbb R$. Then $c$ is periodic with period $k\lambda$, where $k$ is the order of $w$:
--
--   $$
--   c(s+k\lambda)=c(s)\qquad\text{for all }s\in\mathbb R .
--   $$
--
--   **Role.** A curve need not be periodic merely because translating its parameter by $\lambda$ reproduces it up to a symmetry; it is only *equivariantly* periodic. This lemma says that when the symmetry group is finite, genuine periodicity is recovered after $k$ steps, $k$ being the order of the symmetry involved, and — by Lagrange's theorem — $k$ divides the order of the group. It is the mechanism by which a finite symmetry group converts an approximate period into an exact one with controlled arithmetic, which is how a closed path in a quotient by a finite group is lifted to a closed path upstairs whose period is a bounded integer multiple of the original.
--
--   Nothing is assumed about $X$ beyond the action: no topology, no metric, no continuity of $c$.
-- source:
--   Standard spherical geometry; the great-circle facts are the content of the lift used in Lemma 4.6 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608, Section 4 (Spherical Billiards). Mathlib has no parametrized great circle and no geodesics of a sphere.

import Mathlib

theorem Dynamics.periodic_of_shift_smul {X G : Type*} [Group G] [Finite G] [MulAction G X]
    (c : ℝ → X) (w : G) (lam : ℝ) (hshift : ∀ s : ℝ, c (s + lam) = w • c s) :
    Function.Periodic c ((orderOf w : ℕ) * lam) := by sorry
