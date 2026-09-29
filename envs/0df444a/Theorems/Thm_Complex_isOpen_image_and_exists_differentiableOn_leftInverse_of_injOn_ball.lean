-- Prove2me | Theorems.Thm_Complex_isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball
-- name    : Complex.isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/7e30a869-15c1-5e07-9fa9-3849fc7beefe
-- title:
--   Injective holomorphic map on a disc: open image, holomorphic inverse
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$ be a function, $z_0 \in \mathbb{C}$ and $\varepsilon$ a real number with $0 < \varepsilon$, and write $D = B(z_0,\varepsilon)$ for the open metric ball of radius $\varepsilon$ about $z_0$. Assume $f$ is complex differentiable on $D$ (in the sense of `DifferentiableOn ℂ`, i.e. differentiable within $D$ at each point of $D$) and injective on $D$. The conclusion is a conjunction: first, the image $f(D)$ is an open subset of $\mathbb{C}$; second, there exists a function $g : \mathbb{C} \to \mathbb{C}$, complex differentiable on $f(D)$, such that $g(f(z)) = z$ for every $z \in D$, and such that for every $w \in f(D)$ one has both $g(w) \in D$ and $f(g(w)) = w$. Thus $g$ is a global function on $\mathbb{C}$ whose restriction to $f(D)$ is a holomorphic two-sided inverse of $f|_D$, with values in $D$; no assertion is made about $g$ outside $f(D)$.
--
--   This is the one-variable open mapping theorem together with the holomorphic inverse function theorem, packaged as a statement about an injective holomorphic function on a disc. It is used in the construction of local period charts for quaternionic Shimura curves, where an analytic parametrisation injective on a disc must be inverted holomorphically.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Topology

theorem Complex.isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball
    (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ ε)) (hinj : Set.InjOn f (Metric.ball z₀ ε)) :
    IsOpen (f '' Metric.ball z₀ ε) ∧
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (f '' Metric.ball z₀ ε) ∧
      (∀ z ∈ Metric.ball z₀ ε, g (f z) = z) ∧
      (∀ w ∈ f '' Metric.ball z₀ ε, g w ∈ Metric.ball z₀ ε ∧ f (g w) = w) := by sorry
