-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/b441af0d-aae2-5124-94d5-2ed0e639d780
-- title:
--   Patching p-divisibility in ηᵢ across an ideal pair
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring map $\iota\colon \mathbb{W}(\mathbb{F}_{p^2}) \to O$, a formal $O_D$-module $\Phi$ over $O/pO$, a $\mathbb{Z}_p$-algebra $B$ with a ring map $\psi\colon O \to B$, and a rigidified object $t$ over $B$ (a formal $O_D$-module over $B$, an integer, and a pair of power series over $B/pB$). Let $S$ be a Noetherian commutative ring with $p = 0$ in $S$ and $g\colon B \to S$ a ring map, and assume `hc`, that the degree-$0$ and degree-$1$ graded pieces of the Cartier module of `t.XS g` relative to `jS ι ψ g` are complementary submodules; write $D$ for the resulting graded Cartier module data, with underlying module the Cartier module of the law of `t.XS g`, Frobenius and integral Verschiebung, the operator $\varpi$, and those two pieces. Let $L\colon D.M \to D.\mathrm{NMod}$ be a canonical $L$-map: it is $\sigma$-semilinear, satisfies $L(Vx) = [(\varpi x, 0)]$ and $\lambda \circ L = F$, and is compatible, via base change, with a Cartier $L$-map on a special graded Cartier module over a $p$-torsion-free ring surjecting onto $S$. Fix $i \in \{0,1\}$ and $z$ in $\eta_i(L) = \eta(L) \cap N_i$, the degree-$i$ part of the $\eta$-subgroup of $N(D)$. Let $J_0, J_1$ be ideals of $S$ with $J_0 \cap J_1 = 0$. For each $k \in \{0,1\}$ assume a grading hypothesis `hc`$_k$ for the frame obtained by composing $g$ with $S \to S/J_k$, a canonical $L$-map $L_k$ for the associated data $D_k$, an equality $hX_k$ identifying the reduction along $S \to S/J_k$ of the law of `t.XS g` with that of the quotient object, the resulting compatibility of the Cartier-module base-change map with Verschiebung and with $\varpi$, and an element $z_k \in \eta_i(L_k)$ with $p \cdot z_k$ equal to the image of $z$ under the induced map $D.\mathrm{NMod} \to D_k.\mathrm{NMod}$. Then $z$ is divisible by $p$ inside $\eta_i(L)$: there exists $w \in \eta_i(L)$ with $p \cdot w = z$.
--
--   This is the patching step for $p$-divisibility of $\eta$-sections along a pair of ideals with zero intersection, so that $S$ is the fibre product of $S/J_0$ and $S/J_1$ over $S/(J_0+J_1)$, in the style of the strata gluing in Boutot–Carayol. It feeds the localised variant [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot) in the Čerednik–Drinfeld uniformisation package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (t : Rigidified p Φ B)
    {S : Type} [CommRing S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (i : Fin 2)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung i)
    (J₀ J₁ : Ideal S) (hJ : J₀ ⊓ J₁ = ⊥)

    (hc₀ : t.IsGradedS ι ψ ((Ideal.Quotient.mk J₀).comp g))
    (L₀ : ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
    (hX₀ : (t.XS g).F.map (Ideal.Quotient.mk J₀) = (t.XS ((Ideal.Quotient.mk J₀).comp g)).F)
    (hV₀ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₀ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₀ m))
    (hP₀ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₀ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₀ m))
    (z₀ : ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).NMod)
    (hz₀ : z₀ ∈ ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung i)
    (hdiv₀ : p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hX₀) hV₀ hP₀ z)

    (hc₁ : t.IsGradedS ι ψ ((Ideal.Quotient.mk J₁).comp g))
    (L₁ : ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).M →+ ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).NMod) (hL₁ : ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).IsCanonicalLMap L₁)
    (hX₁ : (t.XS g).F.map (Ideal.Quotient.mk J₁) = (t.XS ((Ideal.Quotient.mk J₁).comp g)).F)
    (hV₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m))
    (hP₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m))
    (z₁ : ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).NMod)
    (hz₁ : z₁ ∈ ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁).etaPiece L₁ hL₁.isCartierLMap.map_verschiebung i)
    (hdiv₁ : p • z₁ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hc₁) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hV₁ hP₁ z) :
    ∃ w ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung i, p • w = z := by sorry
