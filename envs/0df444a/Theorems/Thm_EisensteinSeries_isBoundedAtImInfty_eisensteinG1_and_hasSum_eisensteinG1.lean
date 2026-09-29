-- Prove2me | Theorems.Thm_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1
-- name    : EisensteinSeries.isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/e0e677e3-63c7-5e91-858c-f661bdd1468a
-- title:
--   Boundedness at i∞ and q-expansion of g₁^v
-- statement:
--   Let $N$ be a non-zero natural number. For $v=(v_0,v_1)\in\mathbb Z^2$ write $g_1^{v}$ for the function on the upper half-plane given by [`EisensteinSeries.eisensteinG1`](def/EisensteinSeries_WeierstrassZeta.html#L9), namely $$g_1^{v}(\tau)=\frac1N\Bigl(Z\bigl(\tau,\tfrac{v_0\tau+v_1}{N}\bigr)-\frac{v_0\,(\tau\,G_2(\tau)-2\pi i)+v_1\,G_2(\tau)}{N}\Bigr),$$ where $Z(\tau,z)=\frac1z+\sum_{v\in\mathbb Z^2,\,v\neq0}\bigl(\frac1{z-(v_0\tau+v_1)}+\frac1{v_0\tau+v_1}+\frac{z}{(v_0\tau+v_1)^2}\bigr)$ is the Weierstrass zeta function of the lattice $\mathbb Z\tau+\mathbb Z$ (the sum being a `tsum`), and $G_2$ is the function `EisensteinSeries.G2` supplying the quasi-period normalisation. The theorem asserts two statements. First, for every $v\colon\mathrm{Fin}\,2\to\mathbb Z$ such that it is not the case that $N$ divides every component $v_i$, the function $g_1^{v}$ is bounded at $i\infty$ in the sense of `UpperHalfPlane.IsBoundedAtImInfty`. Second, for every $b\in\mathbb Z$ with $N\nmid b$ and every $\tau$ in the upper half-plane, the $\mathbb N$-indexed family whose $n$-th term is $c_n\,e^{2\pi i\tau n}$, with $c_0=\frac{\pi}{N}\cot\bigl(\frac{\pi b}{N}\bigr)$ and, for $n\geq1$, $c_n=-\frac{2\pi i}{N}\sum_{k\mid n}\bigl(e^{2\pi i b k/N}-e^{-2\pi i b k/N}\bigr)$ (the sum over the divisors of $n$), has sum $g_1^{(0,b)}(\tau)$, where $(0,b)$ is the vector `![0, b]`.
--
--   This is the classical analytic input on the weight-one Eisenstein functions $g_1^{v}$ of level $N$: boundedness at the cusp $i\infty$, which together with the transformation law $g_1^{v}(\gamma\tau)=(c\tau+d)\,g_1^{v\gamma}(\tau)$ gives boundedness at all cusps, and the $q$-expansion in the case $v=(0,b)$, which has no fractional powers of $q$. It is used in the construction of weight-one Eisenstein series with nebentypus and their $q$-expansion coefficients, via [`ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd`](thm.html#ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean

import Mathlib
import Definitions.Def_EisensteinSeries_WeierstrassZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem EisensteinSeries.isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1 (N : ℕ) [NeZero N] :
    (∀ v : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        UpperHalfPlane.IsBoundedAtImInfty (EisensteinSeries.eisensteinG1 N v)) ∧
    (∀ (b : ℤ), ¬ (N : ℤ) ∣ b → ∀ τ : UpperHalfPlane,
        HasSum (fun n : ℕ => (if n = 0 then π / N * Complex.cot (π * b / N) else
            -(2 * π * Complex.I) / N * ∑ k ∈ n.divisors,
              (Complex.exp (2 * π * Complex.I * b * k / N) -
                Complex.exp (-(2 * π * Complex.I * b * k / N)))) *
            Complex.exp (2 * π * Complex.I * τ) ^ n)
          (EisensteinSeries.eisensteinG1 N ![0, b] τ)) := by sorry
