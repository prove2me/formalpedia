-- Prove2me | Theorems.Thm_EisensteinSeries_qExpansion_coeff_zero_of_apply_eq_tsum_eisSummand
-- name    : EisensteinSeries.qExpansion_coeff_zero_of_apply_eq_tsum_eisSummand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/e40621a0-4b31-5d46-9a0e-b4f8f63af2e3
-- title:
--   Constant term of the level-N Eisenstein q_N-expansion
-- statement:
--   Let $N$ be a nonzero natural number, let $k$ be a natural number with $3 \le k$, and let $v : \mathrm{Fin}\,2 \to \mathbb{Z}/N$ be a pair of residues. Let $G$ be a modular form of weight $(k : \mathbb{Z})$ for the congruence subgroup $\Gamma(N)$, viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, and assume that for every $\tau$ in the upper half-plane the value $G(\tau)$ is the sum, over all $x : \mathrm{Fin}\,2 \to \mathbb{Z}$ whose reduction modulo $N$ is $v$, of the Eisenstein summands $\mathrm{eisSummand}(k, x, \tau) = 1/(x_0\tau + x_1)^{k}$. The conclusion evaluates the constant term of the $q_N$-expansion of $G$, that is, the coefficient of index $0$ of `UpperHalfPlane.qExpansion (N : ℝ) G`: it equals $\sum_{n \in \mathbb{Z}} 1/(\tilde v_1 + Nn)^{k}$ when $v_0 = 0$, where $\tilde v_1 \in \{0,\dots,N-1\}$ is the canonical representative of $v_1$, and equals $0$ otherwise. In the degenerate case $\tilde v_1 = 0$, $n = 0$ the corresponding term is $0$, by the convention $1/0 = 0$.
--
--   This is the classical computation of the constant term of the weight-$k$, level-$N$ Eisenstein series attached to a pair of residues $v$: only the row $x_0 = 0$ of the lattice sum is independent of $\tau$, the remaining rows contributing no constant term. It is used in the construction of modular forms of weight three and four on the full-level modular curve whose $q$-expansions realise prescribed Tate-curve data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_qExpansion_coeff_zero_of_apply_eq_tsum_eisSummand.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm Real
open Complex

theorem EisensteinSeries.qExpansion_coeff_zero_of_apply_eq_tsum_eisSummand
    (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k) (v : Fin 2 → ZMod N)
    (G : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
    (hG : ∀ τ : UpperHalfPlane,
      G τ = ∑' x : {x : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ x = v}, EisensteinSeries.eisSummand (k : ℤ) x.1 τ) :
    (UpperHalfPlane.qExpansion (N : ℝ) (⇑G)).coeff 0 =
      if v 0 = 0 then ∑' n : ℤ, 1 / ((((v 1).val : ℕ) : ℂ) + (N : ℂ) * (n : ℂ)) ^ k else 0 := by sorry
