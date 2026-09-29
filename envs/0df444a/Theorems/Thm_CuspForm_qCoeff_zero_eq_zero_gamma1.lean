-- Prove2me | Theorems.Thm_CuspForm_qCoeff_zero_eq_zero_gamma1
-- name    : CuspForm.qCoeff_zero_eq_zero_gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/49b2f901-758c-5152-a8d0-4c5a8bb547ab
-- title:
--   Vanishing constant q-coefficient of Γ₁(M) cusp forms
-- statement:
--   Let $M$ be a natural number, $k$ an integer, and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(M)$, in Mathlib's sense: a holomorphic function on the upper half-plane, invariant under the weight-$k$ slash action of $\Gamma_1(M)$, whose slashes by arbitrary elements of $\mathrm{SL}_2(\mathbb{Z})$ tend to $0$ as the imaginary part tends to infinity. The project notion $\mathtt{qCoeff}$ attaches to a function $\mathbb{H} \to \mathbb{C}$ and an index $n$ the $n$-th coefficient of the power series $\mathtt{UpperHalfPlane.qExpansion } 1$, i.e. the $q$-expansion of width $1$, so that $\mathtt{qCoeff } f\ n$ is the coefficient $a_n(f)$ in $f(z) = \sum_{n} a_n(f) q^n$ with $q = e^{2\pi i z}$. The assertion is that for such $f$ the coefficient of index $0$ vanishes: $\mathtt{qCoeff } f\ 0 = 0$. No hypothesis beyond $f$ being a cusp form on $\Gamma_1(M)$ is imposed; in particular $M$ is arbitrary and the weight $k$ is unconstrained.
--
--   This records, in the form used throughout the project's $q$-expansion formalism, the defining property of a cusp form read at the cusp $i\infty$: the constant term of the Fourier expansion is zero. It is used when comparing Hecke eigenvalues with $q$-coefficients, for instance in the identification of the $U_\ell$-eigenvalue of a primitive form with a $q$-coefficient and in the criterion for a form with nebentypus whose Hecke $q$-coefficients are eigenvalues to have non-vanishing first coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_zero_eq_zero_gamma1.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularFormClass

theorem CuspForm.qCoeff_zero_eq_zero_gamma1
    {M : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) :
    ModularFormClass.qCoeff f 0 = 0 := by sorry
