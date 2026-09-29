-- Prove2me | Theorems.Thm_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG
-- name    : EisensteinSeries.exists_modularForm_coe_eq_eisensteinG
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/e1744b9b-f828-54d3-9880-5ef3bfb5dc4b
-- title:
--   Congruence-class Eisenstein series G_kᵃ as a modular form
-- statement:
--   Fix a natural number $N \neq 0$, an integer $k$ with $3 \le k$, and a vector $a \colon \mathrm{Fin}\,2 \to \mathbb{Z}/N\mathbb{Z}$. Here [`EisensteinSeries.eisensteinG N k a`](def/EisensteinSeries_EisensteinG.html#L5) denotes the function on the upper half-plane whose value at $z$ is the unconditional (`tsum`) sum of `eisSummand k v z`, i.e. of $(v_0 z + v_1)^{-k}$, over the subtype of integer vectors $v \colon \mathrm{Fin}\,2 \to \mathbb{Z}$ whose coordinatewise reduction modulo $N$ equals $a$. The theorem asserts two things. First, there exists a modular form $F$ of weight $k$ for the principal congruence subgroup $\Gamma(N)$ — so $F$ is holomorphic on the upper half-plane, invariant in weight $k$ under $\Gamma(N)$, and has the growth condition at the cusps built into `ModularForm` — whose underlying function is exactly [`EisensteinSeries.eisensteinG N k a`](def/EisensteinSeries_EisensteinG.html#L5). Second, for every $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ the weight-$k$ slash action satisfies $G_k^{a} \mid[k]\, \gamma = G_k^{a \cdot \gamma}$, where $a \cdot \gamma$ is the vector–matrix product `a ᵥ* γ` of $a$ with the reduction of $\gamma$ modulo $N$.
--
--   This is the standard fact that, for weight at least $3$, the Eisenstein series attached to a residue class $a \in (\mathbb{Z}/N\mathbb{Z})^2$ is a modular form on $\Gamma(N)$ and that $\mathrm{SL}(2,\mathbb{Z})$ permutes this family according to the right action on residue classes. It supplies the Eisenstein input for the constructions of weight-three and weight-four forms on $\Gamma_1(N)$ with integral $q$-expansions and prescribed slash behaviour, including the Siegel unit construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.lean

import Mathlib
import Definitions.Def_EisensteinSeries_EisensteinG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix
open scoped MatrixGroups CongruenceSubgroup ModularForm

theorem EisensteinSeries.exists_modularForm_coe_eq_eisensteinG
    (N : ℕ) [NeZero N] (k : ℤ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    (∃ F : ModularForm Γ(N) k, ⇑F = EisensteinSeries.eisensteinG N k a) ∧
      ∀ γ : SL(2, ℤ), EisensteinSeries.eisensteinG N k a ∣[k] γ =
        EisensteinSeries.eisensteinG N k (a ᵥ* γ) := by sorry
