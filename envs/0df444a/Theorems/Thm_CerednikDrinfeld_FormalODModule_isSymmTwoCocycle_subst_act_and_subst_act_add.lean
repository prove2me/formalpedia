-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add
-- name    : CerednikDrinfeld.FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/bff506b6-19a6-58a3-84e0-27812eb83813
-- title:
--   Pull-back of symmetric 2-cocycles along the action series
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, $j_0 : \mathbb{Z}_{q^2} \to k$ a ring homomorphism (where $\mathbb{Z}_{q^2}$ denotes `Zp2 q`, the Witt vectors of $\mathbb{F}_{q^2}$), and let $X_0$ be a special formal $\mathcal{O}_D$-module over $k$ relative to $j_0$: a two-dimensional commutative formal group law $F = X_0.F$ over $k$ together with action series $X_0.\mathrm{act}\,a$ ($a \in \mathbb{Z}_{q^2}$) and a series $X_0.\mathrm{varpi}$, all endomorphisms of $F$ in the sense of `IsLawHom`, satisfying the module axioms, the specialness condition at $j_0$ and height $4$. For a pair $\varphi$ of power series in two variables and $\Gamma$ a series in the two blocks of variables, write $\mathrm{pull}\,\varphi\,\Gamma = \Gamma(\varphi(X),\varphi(Y))$, realised by substituting into $\Gamma$ the tuple obtained from $\varphi$ by renaming its variables to the left block, respectively the right block. The assertion is fourfold. First, for every $\varphi$ equal to $X_0.\mathrm{varpi}$ or to $X_0.\mathrm{act}\,a$ for some $a$: $\mathrm{pull}\,\varphi$ sends any $\Gamma$ satisfying `IsSymmTwoCocycle` for $F$ (vanishing constant term, invariance under interchanging the two variable blocks, and the additive $2$-cocycle identity) to such a $\Gamma$; and for every $g$ with vanishing constant term, $\mathrm{subst}\,\varphi\,g$ again has vanishing constant term and $\mathrm{pull}\,\varphi(\partial g) = \partial(\mathrm{subst}\,\varphi\,g)$, where $\partial g = g(F(X,Y)) - g(X) - g(Y)$ is `addCoboundary`. Secondly, $\mathrm{pull}(\mathrm{act}(ab))\Gamma = \mathrm{pull}(\mathrm{act}\,b)(\mathrm{pull}(\mathrm{act}\,a)\Gamma)$ for all $a,b$ and all $\Gamma$. Thirdly, $\mathrm{pull}(\mathrm{act}\,1)$ is the identity. Fourthly, for all $a,b$ and every symmetric two-cocycle $\Gamma$ there exists $g$ with vanishing constant term such that $\mathrm{pull}(\mathrm{act}(a+b))\Gamma = \mathrm{pull}(\mathrm{act}\,a)\Gamma + \mathrm{pull}(\mathrm{act}\,b)\Gamma + \partial g$.
--
--   The four clauses together say that pull-back along the endomorphism series of a special formal $\mathcal{O}_D$-module is well defined on classes of symmetric normalised additive $2$-cocycles modulo coboundaries, and that $a \mapsto (\mathrm{act}\,a)^{*}$ is multiplicative and unital on the nose and additive modulo coboundaries — that is, a $\mathbb{Z}_{q^2}$-module structure on $\mathrm{Ext}^1(F,\mathbb{G}_a)$, with $\mathrm{varpi}$ acting compatibly. It feeds the analysis of deformations over the dual numbers in [`CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and) and [`CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add.lean

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

theorem CerednikDrinfeld.FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ

    (∀ φ : Fin 2 → MvPowerSeries (Fin 2) k, (φ = X₀.varpi ∨ ∃ a, φ = X₀.act a) →
      (∀ Γ, X₀.F.IsSymmTwoCocycle Γ → X₀.F.IsSymmTwoCocycle (pull φ Γ)) ∧
      (∀ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 →
        MvPowerSeries.constantCoeff (MvPowerSeries.subst φ g) = 0 ∧
        pull φ (X₀.F.addCoboundary g) = X₀.F.addCoboundary (MvPowerSeries.subst φ g))) ∧

    (∀ (a b : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k),
      pull (X₀.act (a * b)) Γ = pull (X₀.act b) (pull (X₀.act a) Γ)) ∧
    (∀ Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k, pull (X₀.act 1) Γ = Γ) ∧

    (∀ (a b : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k), X₀.F.IsSymmTwoCocycle Γ →
      ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull (X₀.act (a + b)) Γ = pull (X₀.act a) Γ + pull (X₀.act b) Γ + X₀.F.addCoboundary g) := by sorry
