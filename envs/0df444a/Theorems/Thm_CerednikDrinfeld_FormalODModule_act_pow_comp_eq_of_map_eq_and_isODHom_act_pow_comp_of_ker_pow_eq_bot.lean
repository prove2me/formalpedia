-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot
-- name    : CerednikDrinfeld.FormalODModule.act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/c34a479c-b480-5e41-a5d0-1f53f90ae9f6
-- title:
--   Rigidity of mathcal O_D-linear maps after [p^{nμ}]
-- statement:
--   Fix a prime $p$ and commutative rings $R,S$ in one universe, a ring homomorphism $\pi : R \to S$, a natural number $\mu$ with $(\ker \pi)^{\mu+1} = 0$, and a natural number $n$ with $p^n = 0$ in $R$. Let $X, Y$ be objects of [`CerednikDrinfeld.FormalODModule p R`](def/CerednikDrinfeld_SpecialFormalModule.html#L170): each consists of a two-dimensional formal group law over $R$ together with commutativity, a family `act` of pairs of power series indexed by $W(\mathbb F_{p^2}) =$ `Zp2 p` and a further pair `varpi`, all endomorphisms of the group law, satisfying `act 1 = id`, multiplicativity and additivity of `act`, `varpi ∘ varpi = act p` and `varpi ∘ act a = act (Frobenius a) ∘ varpi`. Write $N = p^{n\mu} \in$ `Zp2 p` and call $\varphi$ an $\mathcal O_D$-morphism $X \to Y$ when `IsODHom` holds: $\varphi$ is a homomorphism of the underlying group laws and commutes with every `act a` and with `varpi`. The theorem asserts two things. First, any two $\mathcal O_D$-morphisms $\varphi, \psi : X \to Y$ with $\pi$-reductions equal coefficientwise satisfy $[N]_Y \circ \varphi = [N]_Y \circ \psi$; here the two `IsODHom` hypotheses are used only through the vanishing of the constant terms. Second, if $\varphi$ is any pair of power series over $R$ with vanishing constant terms whose reduction is an $\mathcal O_D$-morphism $X \otimes_\pi S \to Y \otimes_\pi S$ between the base-changed modules `X.map π`, `Y.map π`, then $[N]_Y \circ \varphi$ is an $\mathcal O_D$-morphism $X \to Y$ over $R$.
--
--   This is the rigidity lemma for $\mathcal O_D$-linear homomorphisms of special formal $\mathcal O_D$-modules along a nilpotent thickening with $p$ nilpotent: for surjective $\pi$ it makes reduction a bijection on $\mathcal O_D$-linear quasi-isogenies, which is what rigidifies a point of Drinfeld's moduli problem. It is used by the statements about `Rigidified` data, in particular the uniqueness of lifts of rigidifications and the comparison of admissible rigidified families with isomorphism classes over Artinian rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot
    (p : ℕ) [Fact p.Prime] {R S : Type u} [CommRing R] [CommRing S] (π : R →+* S) (μ : ℕ)
    (hI : RingHom.ker π ^ (μ + 1) = ⊥) (n : ℕ) (hp : (p : R) ^ n = 0)
    (X Y : CerednikDrinfeld.FormalODModule p R) :
    (∀ φ ψ : CerednikDrinfeld.SpecialFormal.Series R, X.IsODHom Y φ → X.IsODHom Y ψ →
        φ.map π = ψ.map π →
        (Y.act ((p : CerednikDrinfeld.Zp2 p) ^ (n * μ))).comp φ =
          (Y.act ((p : CerednikDrinfeld.Zp2 p) ^ (n * μ))).comp ψ) ∧
    (∀ φ : CerednikDrinfeld.SpecialFormal.Series R, (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
        (X.map π).IsODHom (Y.map π) (φ.map π) →
        X.IsODHom Y ((Y.act ((p : CerednikDrinfeld.Zp2 p) ^ (n * μ))).comp φ)) := by sorry
