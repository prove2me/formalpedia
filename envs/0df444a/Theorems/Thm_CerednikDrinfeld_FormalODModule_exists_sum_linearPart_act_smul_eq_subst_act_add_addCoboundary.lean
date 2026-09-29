-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_act_smul_eq_subst_act_add_addCoboundary
-- name    : CerednikDrinfeld.FormalODModule.exists_sum_linearPart_act_smul_eq_subst_act_add_addCoboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/fc39a31b-1ef9-5839-ab7d-235ef08c0c1f
-- title:
--   ℤ_{q²}-equivariance of a first-order cocycle tuple
-- statement:
--   Fix a prime $q$, a field $k$ of characteristic $q$ and a ring homomorphism $j_0 \colon W(\mathbb{F}_{q^2}) \to k$ from the Witt vectors of the field with $q^2$ elements, written `Zp2 q`. Let $X_0$ be a special formal $\mathcal{O}_D$-module over $k$ relative to $j_0$ (a two-dimensional commutative formal group law $F_0 = X_0.F$ together with an action $a \mapsto X_0.act\,a$ of `Zp2 q` and a uniformiser endomorphism by tuples of power series, satisfying `isSpecial` for $j_0$ and of height $4$), and let $N$ be a formal $\mathcal{O}_D$-module over the dual numbers $k[\varepsilon]$ whose base change along the projection $k[\varepsilon] \to k$ equals $X_0$'s underlying module on the nose. Let $\Gamma \colon \mathrm{Fin}\,2 \to k[[X_1,X_2,Y_1,Y_2]]$ be a tuple each of whose members is a symmetric two-cocycle for $F_0$ (zero constant term, invariant under exchanging the two blocks of variables, and satisfying the additive cocycle identity), and assume that the law of $N$ is the translate of $F_0$ by $\varepsilon\Gamma$, i.e. each component of $N.F$ is obtained by substituting the pair (image of $F_0$ in $k[\varepsilon]$, $\varepsilon$ times the image of $\Gamma$) into the image of the corresponding component of $F_0$. Writing $\mathrm{pull}\,\varphi\,\Gamma_l$ for $\Gamma_l(\varphi(X),\varphi(Y))$, spelled out as a substitution, the conclusion is: for every $a \in$ `Zp2 q` there is a tuple $g$ of power series in two variables with zero constant terms such that for $l = 1,2$ one has $\sum_i \lambda(a)_{li}\,\Gamma_i = \mathrm{pull}\,(X_0.act\,a)\,\Gamma_l + \bigl(g_l(F_0(X,Y)) - g_l(X) - g_l(Y)\bigr)$, where $\lambda(a)$ is the matrix of linear coefficients of the tuple $X_0.act\,a$.
--
--   This is the equivariance statement for the cocycle tuple attached to a first-order deformation of a special formal $\mathcal{O}_D$-module: the $W(\mathbb{F}_{q^2})$-action transforms $\Gamma$ by its linear part, up to an additive coboundary. It is used in the analysis of deformations over the dual numbers, feeding [`CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_act_smul_eq_subst_act_add_addCoboundary.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_sum_linearPart_act_smul_eq_subst_act_add_addCoboundary
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (N : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : ∀ l, X₀.F.IsSymmTwoCocycle (Γ l))
    (hNΓ : ∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    ∀ a : Zp2 q, ∃ g : Fin 2 → MvPowerSeries (Fin 2) k, (∀ l, MvPowerSeries.constantCoeff (g l) = 0) ∧
      ∀ l, ∑ i, MvFormalGroup.linearPart (X₀.act a) l i • Γ i =
        pull (X₀.act a) (Γ l) + X₀.F.addCoboundary (g l) := by sorry
