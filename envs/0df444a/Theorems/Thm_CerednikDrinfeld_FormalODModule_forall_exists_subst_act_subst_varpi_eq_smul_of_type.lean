-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_forall_exists_subst_act_subst_varpi_eq_smul_of_type
-- name    : CerednikDrinfeld.FormalODModule.forall_exists_subst_act_subst_varpi_eq_smul_of_type
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/98e0e63f-2226-5eb1-872d-93a4b8a4c26c
-- title:
--   Pull-back along varpi twists the type by Frobenius
-- statement:
--   Let $q$ be a prime and $k$ a field of characteristic $q$, write $\mathbb{Z}_{q^2} =$ `Zp2 q` for the Witt vectors of the field with $q^2$ elements, and let $j_0 : \mathbb{Z}_{q^2} \to k$ be a ring homomorphism. Let $X_0$ be a special formal $\mathcal{O}_D$-module over $k$ relative to $j_0$: a two-dimensional commutative formal group law $F = X_0.\mathrm{F}$ over $k$ together with an action $a \mapsto X_0.\mathrm{act}\,a$ of $\mathbb{Z}_{q^2}$ by endomorphisms of $F$ (additive and multiplicative in $a$, with $1$ acting as the identity) and an endomorphism $\varpi = X_0.\mathrm{varpi}$ satisfying $\varpi \circ \varpi = [q]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$ for $\sigma =$ `WittVector.frobenius`, subject to the specialness condition at $j_0$ and to height $4$. Let $\chi : \mathbb{Z}_{q^2} \to k$ be a ring homomorphism and let $\Gamma \in k[[X_{\mathrm{inl}\,0},X_{\mathrm{inl}\,1},X_{\mathrm{inr}\,0},X_{\mathrm{inr}\,1}]]$ be a symmetric two-cocycle for $F$, i.e. $\Gamma$ has zero constant term, is invariant under exchanging the left and right pairs of variables, and satisfies the additive cocycle identity for $F$. For a pair $\varphi = (\varphi_0,\varphi_1)$ of power series in two variables, `pull` $\varphi\,\Gamma$ denotes the pull-back $(\varphi\times\varphi)^*\Gamma$, obtained by substituting into $\Gamma$ the series $\varphi_i$ in the left variables for the left block and the series $\varphi_i$ in the right variables for the right block. The assertion is: if for every $a \in \mathbb{Z}_{q^2}$ there is a power series $g$ with zero constant term such that $(X_0.\mathrm{act}\,a)^*\Gamma = \chi(a)\,\Gamma + \delta g$, where $\delta g = g(F(X,Y)) - g(X) - g(Y)$ is the additive coboundary of $g$ for $F$, then for every $a$ there is likewise a power series $g$ with zero constant term such that $(X_0.\mathrm{act}\,a)^*\big(\varpi^*\Gamma\big) = \chi(\sigma a)\,\varpi^*\Gamma + \delta g$.
--
--   This records the compatibility of $\varpi$ with the $\mathbb{Z}_{q^2}$-grading on symmetric two-cocycles modulo coboundaries: pull-back along $\varpi$ shifts the character describing the type of a cocycle by the Frobenius of $\mathbb{Z}_{q^2}$, the formal-cocycle reflection of the relation $\varpi \circ [a] = [\sigma a] \circ \varpi$ in a special formal $\mathcal{O}_D$-module. It feeds the analysis of deformations of special formal $\mathcal{O}_D$-modules, being cited by [`CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_forall_exists_subst_act_subst_varpi_eq_smul_of_type.lean

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

theorem CerednikDrinfeld.FormalODModule.forall_exists_subst_act_subst_varpi_eq_smul_of_type
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) (χ : Zp2 q →+* k) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : X₀.F.IsSymmTwoCocycle Γ) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    (∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull (X₀.act a) Γ = χ a • Γ + X₀.F.addCoboundary g) →
    ∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull (X₀.act a) (pull X₀.varpi Γ) = χ (WittVector.frobenius a) • pull X₀.varpi Γ +
          X₀.F.addCoboundary g := by sorry
