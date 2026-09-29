-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/26ddfe2a-0336-5af5-9f87-616fc2d56843
-- title:
--   Type-χ cocycles killed by varpi^* span at most a line
-- statement:
--   Let $q$ be a prime and $k$ an algebraically closed field of characteristic $q$, let $j_0 \colon \mathbb{Z}_{q^2} \to k$ be a ring homomorphism, where $\mathbb{Z}_{q^2}$ denotes the Witt vectors of the field with $q^2$ elements, and let $X_0$ be a special formal $\mathcal{O}_D$-module over $k$ of height $4$ relative to $j_0$: that is, a commutative two-dimensional formal group law $F = X_0.F$ over $k$ together with series $[a] = X_0.\mathrm{act}\,a$ for $a \in \mathbb{Z}_{q^2}$ and a series $\varpi = X_0.\mathrm{varpi}$, all endomorphisms of $F$, with $[1] = \mathrm{id}$, $[ab] = [a]\circ[b]$, $[a+b] = [a] +_F [b]$, $\varpi \circ \varpi = [q]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$ for the Frobenius $\sigma$, subject to the specialness condition at $j_0$ (the two Lie summands are complementary and invertible) and to $[q]$ having kernel of degree $q^4$. Let $\chi \colon \mathbb{Z}_{q^2} \to k$ be a ring homomorphism, and let $\Gamma, \Gamma'$ be symmetric two-cocycles for $F$, i.e. power series in the two blocks of variables indexed by $\mathrm{Fin}\,2 \oplus \mathrm{Fin}\,2$ with vanishing constant term, invariant under interchanging the two blocks, and satisfying the additive cocycle identity. Write $\varphi^{*}\Gamma$ for the pull-back of $\Gamma$ along a pair of series $\varphi$, obtained by substituting $\varphi$ in the first block of variables and $\varphi$ in the second; and write $\partial g = g(F(X,Y)) - g(X) - g(Y)$ for the additive coboundary of a series $g$ in two variables. Assume that for every $a \in \mathbb{Z}_{q^2}$ one has $[a]^{*}\Gamma = \chi(a)\,\Gamma + \partial g$ and $[a]^{*}\Gamma' = \chi(a)\,\Gamma' + \partial g$ for some $g$ with zero constant term (depending on $a$), and that $\varpi^{*}\Gamma = \partial g$ and $\varpi^{*}\Gamma' = \partial g$ for some such $g$. Then there exist $c, c' \in k$, not both zero, and a series $g$ with zero constant term such that $c\,\Gamma + c'\,\Gamma' = \partial g$.
--
--   This is the dimension bound on the $\chi$-isotypic part of the group of symmetric extension classes of a special formal $\mathcal{O}_D$-module of height $4$ that is annihilated by pull-back along the uniformiser: any two such classes are linearly dependent modulo coboundaries, so the space they span is at most a line. It feeds into [`CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add), in the analysis of deformations of special formal $\mathcal{O}_D$-modules underlying the Čerednik–Drinfeld description.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.lean

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

theorem CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) (χ : Zp2 q →+* k)
    (Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : X₀.F.IsSymmTwoCocycle Γ) (hΓ' : X₀.F.IsSymmTwoCocycle Γ') :
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
    (∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull (X₀.act a) Γ' = χ a • Γ' + X₀.F.addCoboundary g) →
    (∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull X₀.varpi Γ = X₀.F.addCoboundary g) →
    (∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull X₀.varpi Γ' = X₀.F.addCoboundary g) →
    ∃ (c c' : k) (g : MvPowerSeries (Fin 2) k), (c ≠ 0 ∨ c' ≠ 0) ∧ MvPowerSeries.constantCoeff g = 0 ∧
      c • Γ + c' • Γ' = X₀.F.addCoboundary g := by sorry
