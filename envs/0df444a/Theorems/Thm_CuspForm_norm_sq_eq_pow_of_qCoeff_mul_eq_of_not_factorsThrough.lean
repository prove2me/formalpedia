-- Prove2me | Theorems.Thm_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
-- name    : CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/1d164aae-5c7d-5a61-bd4b-77ff3ca98e53
-- title:
--   U_ℓ-eigenvalues at a prime ramified in the nebentypus
-- statement:
--   Let $M \geq 1$ be a natural number, $k$ an integer, and $\varepsilon$ a Dirichlet character modulo $M$ with values in $\mathbb{C}$. Let $\ell$ be a prime dividing $M$ such that $\varepsilon$ does not factor through the reduction map to $\mathbb{Z}/(M/\ell)$, i.e. $\varepsilon$ is not induced by a character modulo $M/\ell$. Let $g$ be a cusp form of weight $k$ for $\Gamma_1(M)$ which is nonzero and has nebentypus $\varepsilon$, in the sense that for every $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ lying in $\Gamma_0(M)$ and every $\tau$ in the upper half-plane one has $g(\gamma \cdot \tau) = \varepsilon(d \bmod M)\,(c\tau + d)^k\, g(\tau)$, where $c = \gamma_{10}$ and $d = \gamma_{11}$ are the entries of the bottom row of $\gamma$. Suppose finally that $a \in \mathbb{C}$ is such that the coefficients of the $q$-expansion of $g$ of width $1$ satisfy $a_{\ell n} = a \cdot a_n$ for all $n \in \mathbb{N}$ (so $g$ is an eigenvector of $U_\ell$ with eigenvalue $a$ in coefficient form). Then $\lVert a\rVert^2 = \ell^{\,k-1}$ as real numbers, the exponent being the integer $k-1$.
--
--   This is the theorem of Li, deduced classically from a result of Ogg: at a prime $\ell \mid M$ whose removal is obstructed by the nebentypus, every $U_\ell$-eigenvalue on cusp forms of weight $k$ and character $\varepsilon$ on $\Gamma_1(M)$ has absolute value $\ell^{(k-1)/2}$. It is used in the analysis of $q$-expansion coefficients of primitive forms at primes dividing the level, in particular in the bounds for $\lVert a_n \rVert$ and in the computation of Hecke eigenvalues at primes dividing the conductor of the character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M)
    (hε : ¬ ε.FactorsThrough (M / ℓ)) (g : CuspForm (Gamma1 M) k) (hg0 : g ≠ 0)
    (hg : CuspForm.HasNebentypus ε g) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff g (ℓ * n) = a * ModularFormClass.qCoeff g n) :
    ‖a‖ ^ 2 = (ℓ : ℝ) ^ (k - 1) := by sorry
