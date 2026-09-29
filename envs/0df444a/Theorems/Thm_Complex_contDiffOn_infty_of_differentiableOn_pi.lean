-- Prove2me | Theorems.Thm_Complex_contDiffOn_infty_of_differentiableOn_pi
-- name    : Complex.contDiffOn_infty_of_differentiableOn_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/08b38a2c-240b-5c01-a2f6-d8ad5c80f867
-- title:
--   Complex differentiability on open U⊆ℂⁿ implies C^∞
-- statement:
--   Let $n$ be a natural number and let $E$ be a complex Banach space, i.e. a normed additive commutative group with a normed $\mathbb{C}$-vector space structure which is complete. Let $f$ be a map from $\mathbb{C}^n$, spelled as the function space `Fin n → ℂ`, to $E$, and let $U$ be a subset of `Fin n → ℂ` which is open. Assume $f$ is $\mathbb{C}$-differentiable on $U$ in the sense of `DifferentiableOn ℂ f U`: at every point of $U$ there is a continuous $\mathbb{C}$-linear map which is a Fréchet derivative of $f$ within $U$ at that point. The conclusion is `ContDiffOn ℂ ∞ f U`, with `∞` the smoothness exponent from the `ContDiff` scope, namely that $f$ is continuously differentiable of every finite order on $U$ relative to the field $\mathbb{C}$: for each $k \in \mathbb{N}$ the iterated Fréchet derivatives of $f$ within $U$ up to order $k$ exist and are continuous on $U$. Note that the conclusion is $C^\infty$-smoothness, not the stronger analyticity exponent.
--
--   This is the $C^\infty$ form of Osgood's lemma in several complex variables: no continuity or local boundedness assumption beyond differentiability is needed to obtain smoothness of all orders. It is obtained from the $C^1$ statement [`Complex.contDiffOn_one_of_differentiableOn_pi`](thm.html#Complex.contDiffOn_one_of_differentiableOn_pi), and is used in the construction of local exponentials for local group laws, in [`LocalGroupLaw.exists_ball_eq_localExp_comp_fderiv_of_map_add`](thm.html#LocalGroupLaw.exists_ball_eq_localExp_comp_fderiv_of_map_add), [`LocalGroupLaw.exists_localExp_family_of_differentiableOn_of_comm_of_assoc`](thm.html#LocalGroupLaw.exists_localExp_family_of_differentiableOn_of_comm_of_assoc) and [`LocalGroupLaw.exists_localExp_of_differentiableOn_of_comm_of_assoc`](thm.html#LocalGroupLaw.exists_localExp_of_differentiableOn_of_comm_of_assoc).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_contDiffOn_infty_of_differentiableOn_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Topology
open scoped ContDiff

theorem Complex.contDiffOn_infty_of_differentiableOn_pi {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U := by sorry
