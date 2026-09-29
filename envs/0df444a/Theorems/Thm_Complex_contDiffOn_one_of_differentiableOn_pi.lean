-- Prove2me | Theorems.Thm_Complex_contDiffOn_one_of_differentiableOn_pi
-- name    : Complex.contDiffOn_one_of_differentiableOn_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/d8613564-cd5b-5bd8-b799-dffe5170697b
-- title:
--   Osgood's lemma: holomorphic maps on ℂⁿ are C¹
-- statement:
--   Let $n$ be a natural number and let $E$ be a complex Banach space, that is, a normed additive commutative group with a normed $\mathbb{C}$-vector space structure which is complete. Let $f \colon (\mathrm{Fin}\,n \to \mathbb{C}) \to E$ be a map defined on the space of $n$-tuples of complex numbers (with its sup-norm product structure) and let $U$ be a subset of that space. Assume $U$ is open and that $f$ is differentiable on $U$ over the field $\mathbb{C}$, i.e. at every point of $U$ it admits a $\mathbb{C}$-linear Fréchet derivative within $U$. The conclusion is that $f$ is continuously differentiable of order $1$ over $\mathbb{C}$ on $U$: `ContDiffOn ℂ 1 f U`. Since $U$ is open, this amounts to saying that $f$ is differentiable on $U$ and that the derivative map $z \mapsto \mathrm{fderiv}_{\mathbb{C}} f\, z \in \mathcal{L}(\mathbb{C}^n, E)$ is continuous on $U$. No hypothesis of continuity or local boundedness beyond differentiability is assumed, and the case $n = 0$ is included.
--
--   This is Osgood's lemma in its weakest form: a complex-differentiable map on an open subset of $\mathbb{C}^n$ with values in a complex Banach space is automatically of class $C^1$, so that the inverse and implicit function theorems apply to it. It is used to upgrade holomorphy statements to smoothness, and in the present development it feeds the corresponding $C^\infty$ statement [`Complex.contDiffOn_infty_of_differentiableOn_pi`](thm.html#Complex.contDiffOn_infty_of_differentiableOn_pi) as well as the construction of differentiable lifts for curve models and for families of uniformisations of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_contDiffOn_one_of_differentiableOn_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.contDiffOn_one_of_differentiableOn_pi {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ 1 f U := by sorry
