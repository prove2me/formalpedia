-- Prove2me | Theorems.Thm_Brouwer_integral_det_one_add_of_eventually_const
-- name    : Brouwer.integral_det_one_add_of_eventually_const
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:15.506475+00:00
-- url     : https://prove2.me/theorems/b2fdf2e7-bde7-4673-90b4-f867d9f20eb9
-- title:
--   A determinant integral constant for small `t` keeps its value at `t = 1`
-- statement:
--   Let $s \subseteq \mathbb{R}^d$ be a measurable set of finite Lebesgue measure and let
--   $x \mapsto A(x)$ be a field of linear maps on $\mathbb{R}^d$, defined for $x \in s$, which is
--   measurable and uniformly bounded in operator norm on $s$. Suppose that for some $t_0 > 0$ the
--   integral of $\det(I + tA)$ over $s$ takes one and the same value $c$ for every $t$ in the
--   interval $(0, t_0)$:
--
--   $$
--   \int_s \det\bigl(I + t\,A(x)\bigr)\,dx \;=\; c \qquad \text{for all } 0 < t < t_0 .
--   $$
--
--   Then the same value is attained at $t = 1$:
--
--   $$
--   \int_s \det\bigl(I + A(x)\bigr)\,dx \;=\; c .
--   $$
--
--   This is a rigidity statement: a quantity of this shape cannot be constant near $0$ and then
--   move. It is the step that converts local information about a perturbation into a statement at
--   full strength $t = 1$, and it is where the finiteness of the measure of $s$ and the uniform
--   bound on $A$ are needed.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.integral_det_one_add_of_eventually_const {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (s : Set (EuclideanSpace ℝ (Fin d))) (hs : MeasurableSet s) (hfin : volume s < ⊤)
    (hA : ∃ C, ∀ x ∈ s, ‖A x‖ ≤ C) (hmeas : AEStronglyMeasurable A (volume.restrict s))
    (c t₀ : ℝ) (ht₀ : 0 < t₀)
    (hconst : ∀ t ∈ Ioo 0 t₀, ∫ x in s, (1 + t • A x).det = c) :
    ∫ x in s, (1 + A x).det = c := by sorry
