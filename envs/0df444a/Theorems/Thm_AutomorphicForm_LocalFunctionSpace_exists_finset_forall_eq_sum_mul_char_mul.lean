-- Prove2me | Theorems.Thm_AutomorphicForm_LocalFunctionSpace_exists_finset_forall_eq_sum_mul_char_mul
-- name    : AutomorphicForm.LocalFunctionSpace.exists_finset_forall_eq_sum_mul_char_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/d9a0340d-6c46-5089-a010-2f4657dfd891
-- title:
--   Finite Fourier expansion of a locally constant function on a p-adic ball
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$ and let $K = \mathbb{Q}_p$ denote the $p$-adic completion at $p$, with its valuation $v$ taking values in $\mathbb{Z}^{\mathrm{mult}} \cup \{0\}$. Let $\chi : K \to \mathbb{C}$ be a function satisfying $\chi(x+y) = \chi(x)\chi(y)$ for all $x, y$, assumed trivial on some ball about $0$ — there is a unit $\gamma_0$ of the value group with $\chi(x) = 1$ whenever $v(x) < \gamma_0$ — and assumed not identically $1$, i.e. $\chi(x_0) \neq 1$ for some $x_0$. Let $f : K \to \mathbb{C}$ be constant on the cosets of a ball: for some unit $\delta$ of the value group, $f(x) = f(y)$ whenever $v(x-y) < \delta$. Then for every unit $\beta$ of the value group there exist a finite subset $T \subseteq K$ and a function $c : K \to \mathbb{C}$ such that $f(x) = \sum_{y \in T} c(y)\,\chi(xy)$ for all $x$ with $v(x) < \beta$. Nothing is asserted outside that ball, and $T$ and $c$ may depend on $\beta$.
--
--   This is finite Fourier analysis on the $p$-adic line: on the ball of radius $\beta$ modulo a ball on which $f$ is constant one has a finite abelian group, whose characters are obtained by translating $\chi$, so that $f$ becomes a finite linear combination of the functions $x \mapsto \chi(xy)$. It is used in the local analysis of admissible representations, being cited in the study of the subspace spanned by differences $\pi(u)w - w$ and in the corresponding statement for Whittaker models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalFunctionSpace_exists_finset_forall_eq_sum_mul_char_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.exists_finset_forall_eq_sum_mul_char_mul
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (χ : p.adicCompletion ℚ → ℂ)
    (hχ : ∀ x y : p.adicCompletion ℚ, χ (x + y) = χ x * χ y)
    (hχ₁ : ∃ γ₀ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x : p.adicCompletion ℚ, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) → χ x = 1)
    (hχ₂ : ∃ x₀ : p.adicCompletion ℚ, χ x₀ ≠ 1)
    (f : p.adicCompletion ℚ → ℂ) (δ : (WithZero (Multiplicative ℤ))ˣ)
    (hf : ∀ x y : p.adicCompletion ℚ, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → f x = f y)
    (β : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ (T : Finset (p.adicCompletion ℚ)) (c : p.adicCompletion ℚ → ℂ),
      ∀ x : p.adicCompletion ℚ, Valued.v x < (β : WithZero (Multiplicative ℤ)) → f x = ∑ y ∈ T, c y * χ (x * y) := by sorry
