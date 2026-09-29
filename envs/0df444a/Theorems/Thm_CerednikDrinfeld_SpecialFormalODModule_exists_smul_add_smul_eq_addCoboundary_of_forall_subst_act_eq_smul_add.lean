-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/2eca8499-f3ee-5f83-8df7-2797697232be
-- title:
--   Each χ-isotypic piece of symmetric cocycles is at most a line
-- statement:
--   Fix a prime $q$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $j_0 \colon \mathbb{Z}_{q^2} = W(\mathbb{F}_{q^2}) \to k$, and let $X_0$ be a special formal $\mathcal{O}_D$-module over $k$ relative to $j_0$: a $2$-dimensional formal group law $F = X_0.\mathtt{F}$ over $k$ which is commutative, together with series $\mathtt{act}(a)$ for $a \in \mathbb{Z}_{q^2}$ and a series $\varpi$, all endomorphisms of $F$, satisfying $\mathtt{act}(1) = \mathrm{id}$, $\mathtt{act}(ab) = \mathtt{act}(a) \circ \mathtt{act}(b)$, $\mathtt{act}(a+b) = \mathtt{act}(a) +_F \mathtt{act}(b)$, $\varpi \circ \varpi = \mathtt{act}(q)$ and $\varpi \circ \mathtt{act}(a) = \mathtt{act}(\sigma a) \circ \varpi$ for the Frobenius $\sigma$ of $\mathbb{Z}_{q^2}$, such that the two Lie summands attached to $j_0$ are complementary and invertible, and such that the kernel of $\mathtt{act}(q)$ has degree $q^4$ (height $4$). Let $\chi \colon \mathbb{Z}_{q^2} \to k$ be a ring homomorphism. For a pair of series $\varphi$ write $\mathrm{pull}(\varphi, \Gamma) = \Gamma(\varphi(X), \varphi(Y))$, the substitution of $\varphi$ into each of the two blocks of variables. The assertion is: for all $\Gamma, \Gamma'$ in $k[[X_1,X_2,Y_1,Y_2]]$ which are symmetric two-cocycles for $F$ (zero constant term, invariance under interchanging the two blocks, and the additive cocycle identity in three blocks of variables), and which are both of type $\chi$, meaning that for every $a \in \mathbb{Z}_{q^2}$ there is a $g$ with $g(0) = 0$ and $\Gamma(\mathtt{act}(a)X, \mathtt{act}(a)Y) = \chi(a)\,\Gamma + \partial g$ with $\partial g = g(F(X,Y)) - g(X) - g(Y)$, and likewise for $\Gamma'$, there exist $c, c' \in k$, not both zero, and $g$ with $g(0) = 0$ such that $c\,\Gamma + c'\,\Gamma' = \partial g$.
--
--   In the language of extensions, $\mathrm{Ext}^1(F, \mathbb{G}_a)$ is computed by symmetric additive two-cocycles modulo coboundaries, and the statement says that the $\chi$-isotypic part of this space for the $\mathbb{Z}_{q^2}$-action by pull-back along the action series is at most one-dimensional; it rests on the bound on the whole space coming from [`MvFormalGroup.exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow`](thm.html#MvFormalGroup.exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow) together with the two results describing the effect of $\varpi$ on cocycles of a fixed type. It feeds the construction, in [`CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and), of a distinguished tuple of cocycles for a special formal $\mathcal{O}_D$-module of height $4$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) (χ : Zp2 q →+* k) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    ∀ (Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k),
      X₀.F.IsSymmTwoCocycle Γ → X₀.F.IsSymmTwoCocycle Γ' →
      (∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
          pull (X₀.act a) Γ = χ a • Γ + X₀.F.addCoboundary g) →
      (∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
          pull (X₀.act a) Γ' = χ a • Γ' + X₀.F.addCoboundary g) →
      ∃ (c c' : k) (g : MvPowerSeries (Fin 2) k), (c ≠ 0 ∨ c' ≠ 0) ∧ MvPowerSeries.constantCoeff g = 0 ∧
        c • Γ + c' • Γ' = X₀.F.addCoboundary g := by sorry
