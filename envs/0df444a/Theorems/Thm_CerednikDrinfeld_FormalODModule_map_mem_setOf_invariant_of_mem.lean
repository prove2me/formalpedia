-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_map_mem_setOf_invariant_of_mem
-- name    : CerednikDrinfeld.FormalODModule.map_mem_setOf_invariant_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/a8d35e6d-bc1e-55f6-a0f7-5b32d01796c8
-- title:
--   Base change preserves J-invariant power series
-- statement:
--   Fix a prime $p$ (as a natural number with the primality instance), commutative rings $R$ and $R'$, a formal $\mathcal{O}_D$-module $X$ over $R$ in the sense of the structure `FormalODModule` (a two-dimensional formal group law $X.F$ over $R$, assumed commutative, together with an action of $\mathbb{Z}_{p^2}$ and a uniformiser series $\varpi$ satisfying the law-homomorphism and composition identities), an ideal $J$ of $R[\![x_0,x_1]\!] =$ `MvPowerSeries (Fin 2) R`, a ring homomorphism $\psi : R \to R'$, and a power series $w \in R[\![x_0,x_1]\!]$. Assume $w$ lies in $J$ and that $$\operatorname{subst}(X.F.\mathrm{toPowerSeries})(w) - \operatorname{subst}(l \mapsto X_{\mathrm{inl}\,l})(w)$$ lies in the ideal of $R[\![x,y]\!] =$ `MvPowerSeries (Fin 2 ⊕ Fin 2) R` spanned by the image of $J$ under substitution of the variables $X_{\mathrm{inr}\,l}$; that is, $w(F(x,y)) - w(x) \in (J(y))$. The conclusion is that the coefficientwise base change `MvPowerSeries.map ψ w` satisfies the same two conditions over $R'$, with $J$ replaced by its image ideal $J \cdot$ `map` $\psi$ and $X.F$ replaced by the group law of $X$`.map` $\psi$, whose power series are the coefficientwise images $\psi_*(X.F.\mathrm{toPowerSeries}\,i)$.
--
--   This is the functoriality of the 'invariance modulo $J$' condition cutting out formal subgroup-like ideals: the set of $w$ satisfying the two displayed conditions is stable under base change of the coefficient ring along $\psi$, with both the ideal and the formal group law transported. It is used in the construction of non-free invariant elements and of invariant pairs with prescribed coefficient congruences for maximal ideals in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_map_mem_setOf_invariant_of_mem.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.map_mem_setOf_invariant_of_mem
    (p : ℕ) [Fact p.Prime] {R R' : Type} [CommRing R] [CommRing R'] (X : FormalODModule p R)
    (J : Ideal (MvPowerSeries (Fin 2) R)) (ψ : R →+* R') (w : MvPowerSeries (Fin 2) R)
    (hw : w ∈ {w : MvPowerSeries (Fin 2) R | w ∈ J ∧
          MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R))) '' (J : Set (MvPowerSeries (Fin 2) R)))}) :
    MvPowerSeries.map ψ w ∈ {w : MvPowerSeries (Fin 2) R' | w ∈ (J.map (MvPowerSeries.map ψ)) ∧
          MvPowerSeries.subst (X.map ψ).F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R')) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R'))) '' ((J.map (MvPowerSeries.map ψ)) : Set (MvPowerSeries (Fin 2) R')))} := by sorry
