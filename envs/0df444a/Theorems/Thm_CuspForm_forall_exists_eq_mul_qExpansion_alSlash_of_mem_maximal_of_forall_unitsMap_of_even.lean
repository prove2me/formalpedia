-- Prove2me | Theorems.Thm_CuspForm_forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even
-- name    : CuspForm.forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/996158f5-4cde-5764-aca3-43b049a5f851
-- title:
--   Atkin–Lehner transform preserves 𝔪-local q-expansions
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number, let $H$ be a subgroup of $(\mathbb Z/M)^\times$, and assume $p \mid M$ but $p^2 \nmid M$, and that every unit of $\mathbb Z/M$ whose reduction modulo $M/p$ equals $1$ lies in $H$. Let $W$ be an Atkin–Lehner datum for the pair $(M, M/p)$, that is, a natural number $R$ with $M = (M/p)\,R$ together with integers $a,b$ satisfying $(M/p)a - Rb = 1$; write $\,\cdot\,\mid[k]\,W$ for the weight-$k$ slash action by the associated real matrix `W.alGL`, as packaged by [`ModularForm.alSlash`](def/ModularForm_AtkinLehnerDatum.html#L141). Let $k$ be an even integer and $f$ a cusp form of weight $k$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $SL(2,\mathbb Z)$, namely the image in $SL(2,\mathbb Z)$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb Z/M)^\times$ given by the lower-right entry modulo $M$. Let $\mathfrak m$ be a maximal ideal of the integral closure $\bar{\mathbb Z}$ of $\mathbb Z$ in $\mathbb C$ containing $p$, and suppose that each coefficient $a_n(f)$ of the $q$-expansion of $f$ of period $1$ is $\mathfrak m$-local in the sense that there are $x,y \in \bar{\mathbb Z}$ with $y \notin \mathfrak m$ and $x = y\, a_n(f)$. Then the same holds for $f \mid[k] W$: for every $n$ there are $x,y \in \bar{\mathbb Z}$ with $y \notin \mathfrak m$ and $x = y\, a_n(f \mid[k] W)$.
--
--   This is the statement that the Atkin–Lehner operator at the exactly dividing prime $p$ preserves $\mathfrak m$-local integrality of $q$-expansions at the cusp $\infty$, for even weight and a level group $\Gamma_H(M)$ whose $H$ contains all units congruent to $1$ modulo $M/p$. It is used in the level-lowering analysis of cusp forms of weight $2$, where the Atkin–Lehner transform of a form with $\mathfrak m$-integral expansion must again be handled integrally at $\mathfrak m$, and feeds the results on the two-cusp integral set and on vanishing of forms all of whose coefficients lie in $\mathfrak m$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p)) {k : ℤ} (f : CuspForm (CohCarrier.GammaH M H) k) (hk : Even k)
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪)
    (hf : ∀ n : ℕ, ∃ x y : ↥(integralClosure ℤ ℂ), y ∉ 𝔪 ∧ (x : ℂ) = y * (UpperHalfPlane.qExpansion 1 ⇑f).coeff n) :
    ∀ n : ℕ, ∃ x y : ↥(integralClosure ℤ ℂ), y ∉ 𝔪 ∧
      (x : ℂ) = y * (UpperHalfPlane.qExpansion 1 (ModularForm.alSlash W k ⇑f)).coeff n := by sorry
