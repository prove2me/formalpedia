-- Prove2me | Theorems.Thm_EisensteinSeries_qExpansion_coeff_of_apply_eq_tsum_eisSummand
-- name    : EisensteinSeries.qExpansion_coeff_of_apply_eq_tsum_eisSummand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/df47f9ef-21e9-56cc-9d7e-3979dbf09c86
-- title:
--   q_N-expansion coefficients of level-N Eisenstein series
-- statement:
--   Let $N$ be a nonzero natural number, $k$ a natural number with $3 \le k$, and $v : \mathrm{Fin}\,2 \to \mathbb{Z}/N$. Let $G$ be a modular form of weight $(k : \mathbb{Z})$ for the congruence subgroup $\Gamma(N)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, and assume that for every $\tau$ in the upper half plane the value $G(\tau)$ is the sum, over the subtype of those $x : \mathrm{Fin}\,2 \to \mathbb{Z}$ whose reduction modulo $N$ equals $v$, of the Eisenstein summands $\mathrm{eisSummand}(k, x, \tau) = (x_0\tau + x_1)^{-k}$ (the sum being an unconditional `tsum`). Then for every natural number $n \ge 1$ the $n$-th coefficient of the $q$-expansion of $G$ with period $N$, i.e. of its expansion in $q_N = e^{2\pi i \tau/N}$, equals $$\frac{(-2\pi i)^k}{(k-1)!\,N^k}\sum_{(m,d)} d^{\,k-1}\Bigl(\mathbf{1}[\,m \equiv v_0 \ (N)\,]\,e^{2\pi i\, d\,\widetilde{v_1}/N} + (-1)^k\,\mathbf{1}[\,m \equiv -v_0\ (N)\,]\,e^{-2\pi i\, d\,\widetilde{v_1}/N}\Bigr),$$ the sum running over the pairs $(m,d)$ of positive integers in `Nat.divisorsAntidiagonal n`, so $md = n$, where $\widetilde{v_1}$ denotes the canonical representative `(v 1).val` of $v_1$ in $\{0,\dots,N-1\}$ and the congruences are the conditions that the image of $m$ in $\mathbb{Z}/N$ be $v_0$, resp. $-v_0$. No assertion is made about the constant coefficient.
--
--   This is the classical Fourier expansion of the full-lattice Eisenstein series of weight $k$ and level $N$ attached to a residue vector $v \in (\mathbb{Z}/N)^2$, as in Diamond–Shurman (4.6)–(4.7), here in the form of a formula for the coefficients of index $n \ge 1$ of the $q_N$-expansion. It is used to produce modular forms of weight three and four on modular curves of full level (and of $\Gamma_H$ type) with prescribed $q$-expansions, in particular the forms matching the Tate curve data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_qExpansion_coeff_of_apply_eq_tsum_eisSummand.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm Real
open Complex

theorem EisensteinSeries.qExpansion_coeff_of_apply_eq_tsum_eisSummand
    (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k) (v : Fin 2 → ZMod N)
    (G : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
    (hG : ∀ τ : UpperHalfPlane,
      G τ = ∑' x : {x : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ x = v}, EisensteinSeries.eisSummand (k : ℤ) x.1 τ)
    (n : ℕ) (hn : 1 ≤ n) :
    (UpperHalfPlane.qExpansion (N : ℝ) (⇑G)).coeff n =
      ((-2 * π * I) ^ k / ((k - 1).factorial * (N : ℂ) ^ k)) *
        ∑ md ∈ Nat.divisorsAntidiagonal n,
          (md.2 : ℂ) ^ (k - 1) *
            ((if ((md.1 : ℕ) : ZMod N) = v 0 then Complex.exp (2 * π * I * ((md.2 * (v 1).val : ℕ) : ℂ) / N) else 0) +
              (-1) ^ k * (if ((md.1 : ℕ) : ZMod N) = -v 0 then Complex.exp (-(2 * π * I * ((md.2 * (v 1).val : ℕ) : ℂ) / N)) else 0)) := by sorry
