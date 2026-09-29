-- Prove2me | Theorems.Thm_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero
-- name    : AutomorphicForm.LocalFunctionSpace.eq_of_forall_exists_forall_sum_char_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/fb4fb242-6f40-5cd1-8ace-4bd90c24bb40
-- title:
--   Constancy from vanishing of all twisted finite window sums
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$ and write $K$ for the completion `p.adicCompletion ℚ` of $\mathbb{Q}$ at $p$, with its valuation `Valued.v` taking values in $\mathbb{Z}^{\mathrm{mult}}\cup\{0\}$; the radii $\delta,\gamma_0,\beta_0,\beta$ below range over the units of that value monoid, i.e. over nonzero values. Let $f : K \to \mathbb{C}$ be uniformly locally constant, in the sense that there is a radius $\delta$ with $f x = f y$ whenever $v(x-y) < \delta$. Let $\chi : K \to \mathbb{C}$ satisfy $\chi(x+y) = \chi(x)\chi(y)$ for all $x,y$, be equal to $1$ on some ball $\{v(x) < \gamma_0\}$ about $0$, and satisfy $\chi(x_0) \neq 1$ for at least one $x_0$. Assume finally that for every $a \neq 0$ in $K$ there is $\beta_0$ such that for every $\beta \geq \beta_0$ there is $\delta$ with the following property: for every finite subset $T$ of the ball $\{v(t) < \beta\}$ such that every $x$ with $v(x) < \beta$ satisfies $v(x - t) < \delta$ for exactly one $t \in T$, one has $\sum_{t \in T} \chi(-(a t))\, f(t) = 0$. Then $f$ is constant: $f x = f y$ for all $x, y \in K$.
--
--   This is a statement of finite Fourier analysis on the additive group of a $p$-adic field: vanishing of all the finite Riemann-type sums $\sum_{t}\chi(-at)f(t)$ over nets in large balls, for every nonzero frequency $a$, forces the locally constant function $f$ to have trivial Fourier transform away from $a=0$, hence to be constant. It is used in the analysis of local function spaces attached to representations of $\mathrm{GL}(2)$ over a $p$-adic field, and is cited by [`AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_diagonal_mul_mem_span_sub`](thm.html#AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_diagonal_mul_mem_span_sub).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.eq_of_forall_exists_forall_sum_char_mul_eq_zero
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (f : p.adicCompletion ℚ → ℂ)
    (hf : ∃ δ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x y : p.adicCompletion ℚ, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → f x = f y)
    (χ : p.adicCompletion ℚ → ℂ)
    (hχ : ∀ x y : p.adicCompletion ℚ, χ (x + y) = χ x * χ y)
    (hχ₁ : ∃ γ₀ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x : p.adicCompletion ℚ, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) → χ x = 1)
    (hχ₂ : ∃ x₀ : p.adicCompletion ℚ, χ x₀ ≠ 1)
    (hsum : ∀ a : p.adicCompletion ℚ, a ≠ 0 →
      ∃ β₀ : (WithZero (Multiplicative ℤ))ˣ, ∀ β : (WithZero (Multiplicative ℤ))ˣ, β₀ ≤ β →
      ∃ δ : (WithZero (Multiplicative ℤ))ˣ, ∀ T : Finset (p.adicCompletion ℚ),
        (∀ t ∈ T, Valued.v t < (β : WithZero (Multiplicative ℤ))) →
        (∀ x : p.adicCompletion ℚ, Valued.v x < (β : WithZero (Multiplicative ℤ)) →
          ∃! t, t ∈ T ∧ Valued.v (x - t) < (δ : WithZero (Multiplicative ℤ))) →
        ∑ t ∈ T, χ (-(a * t)) * f t = 0) :
    ∀ x y : p.adicCompletion ℚ, f x = f y := by sorry
