-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isODHom_of_comp_eq_act_pow_of_subst_injective
-- name    : CerednikDrinfeld.FormalODModule.isODHom_of_comp_eq_act_pow_of_subst_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/6e80235d-389f-5e3f-889e-3046a3d96b80
-- title:
--   Cancelling an isogeny: β is an mathcal O_D-homomorphism
-- statement:
--   Let $p$ be a prime and $B$ a commutative ring, and let $X,Y$ be formal $\mathcal O_D$-modules over $B$ in the sense of the structure `FormalODModule`: a commutative $2$-dimensional formal group law together with an action `act` of $\mathbb Z_{p^2}=W(\mathbb F_{p^2})$ and a series `varpi`, all endomorphisms of the law, with `act` multiplicative and additive in the appropriate sense, $\varpi\circ\varpi=\mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$ for the Witt-vector Frobenius $\sigma$. Let $\rho,\beta$ be pairs of power series in two variables over $B$ and $N$ a natural number. Assume: $\rho$ is an $\mathcal O_D$-homomorphism $X\to Y$, i.e. a homomorphism of the two laws commuting with both actions and with $\varpi$; substitution of $\rho$, $H\mapsto H\circ\rho$, is injective on $B[\![x_1,x_2]\!]$; substitution of the two-block series $\rho\times\rho$ is injective on $B[\![x_1,x_2,x_1',x_2']\!]$; each $\beta_i$ has zero constant term; and $\beta\circ\rho=\mathrm{act}_X\!\big((p)^N\big)$, the action of $p^N\in\mathbb Z_{p^2}$ on $X$. Then $\beta$ is an $\mathcal O_D$-homomorphism $Y\to X$: a homomorphism of the laws commuting with the $\mathbb Z_{p^2}$-actions and with $\varpi$.
--
--   This is the cancellation step used to produce a quasi-inverse isogeny: once some $\beta$ satisfying $\beta\circ\rho=[p^N]_X$ has been found at the level of power series, it is automatically a morphism of formal $\mathcal O_D$-modules. It is invoked in the construction of such a $\beta$ for isogenies of given height over a field and over Noetherian base rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isODHom_of_comp_eq_act_pow_of_subst_injective.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.isODHom_of_comp_eq_act_pow_of_subst_injective
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (X Y : FormalODModule p B) (ρ β : Series B) (N : ℕ)
    (hρ : FormalODModule.IsODHom X Y ρ)
    (hinj : ∀ H H' : MvPowerSeries (Fin 2) B, MvPowerSeries.subst ρ H = MvPowerSeries.subst ρ H' → H = H')
    (hinj2 : ∀ H H' : MvPowerSeries (Fin 2 ⊕ Fin 2) B,
      MvPowerSeries.subst (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))) H =
      MvPowerSeries.subst (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))) H' → H = H')
    (hβ0 : ∀ i, MvPowerSeries.constantCoeff (β i) = 0)
    (hβρ : β.comp ρ = X.act ((p : Zp2 p) ^ N)) :
    FormalODModule.IsODHom Y X β := by sorry
