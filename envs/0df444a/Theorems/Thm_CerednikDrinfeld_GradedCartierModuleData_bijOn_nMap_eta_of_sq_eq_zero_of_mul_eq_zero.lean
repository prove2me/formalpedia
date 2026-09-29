-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero
-- name    : CerednikDrinfeld.GradedCartierModuleData.bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/2bea714b-dd9a-5b81-b17b-6b977f9554e8
-- title:
--   η is invariant under square-zero thickenings killed by p
-- statement:
--   Let $p$ be a prime, let $B$ and $B'$ be commutative rings, let $j\colon \mathbb{W}(\mathbb{F}_{p^2})\to B$ be a ring homomorphism (`Zp2 p` being the Witt vectors of the field of $p^2$ elements), and let $\varphi\colon B\to B'$ be a surjective ring homomorphism whose kernel $I$ satisfies $I\cdot I=\bot$ and $px=0$ for every $x\in I$. Let $D$ be a graded Cartier module datum over $(B,j)$ and $D'$ one over $(B',\varphi\circ j)$ — that is, a $\mathbb{W}(B)$-module $M$ with additive endomorphisms $F$, $V$, a $\mathbb{W}(B)$-linear $\varpi$ and a pair of complementary submodules indexed by $\mathrm{Fin}\,2$, subject to the usual semilinearity, $FV=p$, $\varpi^2=p$, commutation and degree-shifting relations — and assume both are special, i.e. each possesses a homogeneous $V$-basis and is $V$-adically complete. Let $f\colon D.M\to D'.M$ be additive and a base change along $\varphi$: semilinear for $\mathbb{W}(\varphi)$, compatible with $F$, $V$, $\varpi$ and the grading, and carrying some homogeneous $V$-basis of $D$ to one of $D'$. Let $L\colon D.M\to D.\mathrm{NMod}$ and $L'\colon D'.M\to D'.\mathrm{NMod}$ be canonical $L$-maps (Cartier $L$-maps, so in particular $L(Vx)$ is the class of $(\varpi x,0)$, admitting a lift to a special Cartier module over a $p$-torsion-free ring surjecting onto the base), and assume $L'\circ f = N(f)\circ L$, where $N(f)$ denotes the induced map `nMap` on the quotients $\mathrm{NMod}=(M\times\Sigma)/\mathrm{nRel}$. Then $N(f)$ maps the subgroup $\eta(L)$ of elements of $D.\mathrm{NMod}$ fixed by the operator `phi` attached to $L$ bijectively onto the corresponding subgroup $\eta(L')$ of $D'.\mathrm{NMod}$.
--
--   This is the inductive step in the proof that Drinfeld's functor $\eta$, attached to a special formal $\mathcal{O}_D$-module through its graded Cartier module, is unchanged under a nilpotent thickening of the base killed by a power of $p$: the general case is obtained by filtering the kernel so that each successive quotient is square-zero and killed by $p$. It is used for the bijectivity of $\eta$ along surjections with nilpotent kernel and in the comparison of $\eta$ with base change for formal $\mathcal{O}_D$-modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (φ : B →+* B') (hφ : Function.Surjective φ)
    (hI2 : RingHom.ker φ * RingHom.ker φ = ⊥) (hIp : ∀ x ∈ RingHom.ker φ, (p : B) * x = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L')
    (hLL' : ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x)) :
    Set.BijOn (D.nMap D' f hf.2.2.1 hf.2.2.2.1)
      (D.eta L hL.isCartierLMap.map_verschiebung : Set D.NMod)
      (D'.eta L' hL'.isCartierLMap.map_verschiebung : Set D'.NMod) := by sorry
