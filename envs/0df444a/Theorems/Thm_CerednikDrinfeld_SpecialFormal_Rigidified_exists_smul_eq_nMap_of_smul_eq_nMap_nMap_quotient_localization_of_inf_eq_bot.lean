-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/ac159192-6190-520a-b073-d4f018fdd279
-- title:
--   Patching p-divisions of ηⱼ-classes over a Milnor square
-- statement:
--   Fix a prime $p$ and a commutative ring $O$ together with a ring homomorphism $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$ (the source being `Zp2 p`, the Witt vectors of the field with $p^2$ elements), a formal $O_D$-module $\Phi$ over $O/pO$, a commutative ring $B$ that is a $\mathbb{Z}_p$-algebra, a ring homomorphism $\psi : O \to B$, and a rigidified datum $t :$ `Rigidified p Φ B`, i.e. a formal $O_D$-module $t.X$ over $B$ together with a natural number and a pair of power series over $B/pB$. Fix further a Noetherian commutative ring $S$, a ring homomorphism $g : B \to S$ with $p = 0$ in $S$ (hypothesis `hS`), and a point $x \in \operatorname{Spec} S$.
--
--   For a ring homomorphism out of $B$ the notation `t.XS` produces the corresponding formal module over the target; the Cartier module of its underlying formal group law carries the Verschiebung `verschiebungInt`, the Frobenius, and the linear operator `varpi` induced by the uniformiser endomorphism of the formal module, as well as the graded pieces `gradedPiece` of degrees $0$ and $1$ relative to the structure map `jS ι ψ` (the degree-$n$ piece consists of those Cartier module elements on which the Teichmüller action of each $c \in \mathbb{F}_{p^2}$ agrees with the homothety by the $p^n$-th power of the image of the Teichmüller lift of $c$). The predicate `IsGradedS` asserts that these two pieces are complementary submodules over the Witt vectors of the target, which is exactly the datum needed to form `toGradedCartierModuleData`; for such data, `NMod` is the quotient of $M \times \Sigma$ (where $\Sigma$ is $M$ with the Witt action twisted by Frobenius) by the submodule `nRel`, `nPiece i` is the image in `NMod` of the product of the degree-$i$ piece with itself, and `etaPiece L hL i` is the intersection of the subgroup `eta L` with `nPiece i`. Given two such graded data and an additive map between their $M$'s commuting with Verschiebung and with `varpi`, `nMap` is the induced additive map on the `NMod`'s.
--
--   The hypotheses over $S$ itself are: `hc`, stating `t.IsGradedS ι ψ g`; an additive map $L$ from the $M$ of $D :=$ `(t.XS g).toGradedCartierModuleData _ hc` to its `NMod`, with `hL` asserting that $L$ is a canonical $L$-map (a Cartier $L$-map — Frobenius-semilinear, sending $V x$ to the class of $(\varpi x, 0)$ and composing with $\lambda$ to the Frobenius — which in addition descends from a Cartier $L$-map on a special Cartier module over a $p$-torsion-free surjective cover); an index $j \in \{0,1\}$; and an element $z$ of $D$'s `NMod` lying in `etaPiece L hL.isCartierLMap.map_verschiebung j`. Finally, two ideals $J_0, J_1 \subseteq S$ are given with $J_0 \cap J_1 = 0$ (hypothesis `hJ`).
--
--   For each $k \in \{0,1\}$ a block of hypotheses is imposed, describing a $p$-division of the image of $z$ on the $k$-th stratum, localised near $x$. The block consists of: `hcq`$_k$, that `t.IsGradedS ι ψ` holds for $g$ followed by the quotient map $S \to S/J_k$; `hXq`$_k$, that the formal group law of `t.XS g` pushed forward along $S \to S/J_k$ equals the formal group law of `t.XS` of the composite; `hVq`$_k$ and `hPq`$_k$, that the induced base change map `baseChangeEq` on Cartier modules commutes with Verschiebung and with `varpi`; a point $x_k' \in \operatorname{Spec}(S/J_k)$ whose contraction along $S \to S/J_k$ is the prime of $x$; an element $f_k' \in S/J_k$ outside the prime of $x_k'$; `hc`$_k'$, that `t.IsGradedS ι ψ` holds for $g$ followed by $S \to S/J_k \to (S/J_k)_{f_k'}$ (the localisation away from $f_k'$); an additive map $L_k'$ on the corresponding graded Cartier module data over $(S/J_k)_{f_k'}$ together with `hL`$_k'$, that it is a canonical $L$-map; `hX`$_k'$, `hV`$_k'$, `hP`$_k'$, the analogous compatibilities of the formal group law and of the base change map with Verschiebung and `varpi` for $S/J_k \to (S/J_k)_{f_k'}$; an element $z_k'$ of the `NMod` over $(S/J_k)_{f_k'}$ lying in `etaPiece L`$_k'$ at the index $j$; and `heq`$_k$, the equation
--   $$p \cdot z_k' = \mathrm{nMap}\bigl(\mathrm{nMap}(z)\bigr),$$
--   where the inner `nMap` is taken along the base change $S \to S/J_k$ and the outer one along $S/J_k \to (S/J_k)_{f_k'}$, each with the compatibilities just listed.
--
--   The conclusion asserts the existence of: an element $f_0 \in S$; a proof that $f_0$ does not lie in the prime ideal of $x$; a proof `hc₀` that `t.IsGradedS ι ψ` holds for $g$ followed by $S \to$ `Localization.Away f₀`; an additive map $L_0$ from the $M$ of `(t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀` to its `NMod`, together with a proof `hL₀` that $L_0$ is a canonical $L$-map; a proof `hXr` that the formal group law of `t.XS g` pushed forward along $S \to$ `Localization.Away f₀` is the formal group law of `t.XS` of the composite; proofs `hrV` and `hrPi` that the base change map `baseChangeEq` attached to `hXr` commutes with Verschiebung and with `varpi`; and an element $z_0$ of the `NMod` over `Localization.Away f₀` such that both
--
--   (i) $z_0$ lies in `etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j`, and
--
--   (ii) $p \cdot z_0$ equals the image of $z$ under the map `nMap` from the data over $S$ to the data over `Localization.Away f₀` determined by `baseChangeEq _ hXr`, `hrV` and `hrPi`.
--
--   This is the local patching step in the descent of $p$-divisibility of $\eta_j$-classes across a Milnor square: the vanishing hypothesis $J_0 \cap J_1 = 0$ makes $S$ a subring of $S/J_0 \times S/J_1$, and a $p$-division of the image of $z$ given on each stratum near $x$ is glued into a $p$-division over a basic open neighbourhood $D(f_0)$ of $x$. It is used by [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced), where the strata arise from a decomposition of a reduced Noetherian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (t : Rigidified p Φ B)
    {S : Type} [CommRing S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    (J₀ J₁ : Ideal S) (hJ : J₀ ⊓ J₁ = ⊥)

    (hcq₀ : t.IsGradedS ι ψ ((Ideal.Quotient.mk J₀).comp g))
    (hXq₀ : (t.XS g).F.map (Ideal.Quotient.mk J₀) = (t.XS ((Ideal.Quotient.mk J₀).comp g)).F)
    (hVq₀ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ m))
    (hPq₀ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ m))
    (x₀' : PrimeSpectrum (S ⧸ J₀)) (hx₀' : x₀'.asIdeal.comap (Ideal.Quotient.mk J₀) = x.asIdeal)
    (f₀' : S ⧸ J₀) (hf₀' : f₀' ∉ x₀'.asIdeal)
    (hc₀' : t.IsGradedS ι ψ ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g)))
    (L₀' : ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').M →+ ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').NMod) (hL₀' : ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').IsCanonicalLMap L₀')
    (hX₀' : (t.XS ((Ideal.Quotient.mk J₀).comp g)).F.map (algebraMap (S ⧸ J₀) (Localization.Away f₀')) = (t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).F)
    (hV₀' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₀' (((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).verschiebung m) =
      ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₀' m))
    (hP₀' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₀' (((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).varpi m) =
      ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₀' m))
    (z₀' : ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').NMod) (hz₀' : z₀' ∈ ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').etaPiece L₀' hL₀'.isCartierLMap.map_verschiebung j)
    (heq₀ : p • z₀' = ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).nMap ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hX₀') hV₀' hP₀'
      (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXq₀) hVq₀ hPq₀ z))

    (hcq₁ : t.IsGradedS ι ψ ((Ideal.Quotient.mk J₁).comp g))
    (hXq₁ : (t.XS g).F.map (Ideal.Quotient.mk J₁) = (t.XS ((Ideal.Quotient.mk J₁).comp g)).F)
    (hVq₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ m))
    (hPq₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ m))
    (x₁' : PrimeSpectrum (S ⧸ J₁)) (hx₁' : x₁'.asIdeal.comap (Ideal.Quotient.mk J₁) = x.asIdeal)
    (f₁' : S ⧸ J₁) (hf₁' : f₁' ∉ x₁'.asIdeal)
    (hc₁' : t.IsGradedS ι ψ ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g)))
    (L₁' : ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').M →+ ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').NMod) (hL₁' : ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').IsCanonicalLMap L₁')
    (hX₁' : (t.XS ((Ideal.Quotient.mk J₁).comp g)).F.map (algebraMap (S ⧸ J₁) (Localization.Away f₁')) = (t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).F)
    (hV₁' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁' (((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).verschiebung m) =
      ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₁' m))
    (hP₁' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁' (((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).varpi m) =
      ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₁' m))
    (z₁' : ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').NMod) (hz₁' : z₁' ∈ ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').etaPiece L₁' hL₁'.isCartierLMap.map_verschiebung j)
    (heq₁ : p • z₁' = ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).nMap ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁') (MvFormalGroup.CartierModule.baseChangeEq _ hX₁') hV₁' hP₁'
      (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁) (MvFormalGroup.CartierModule.baseChangeEq _ hXq₁) hVq₁ hPq₁ z)) :
    ∃ (f₀ : S) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
      (L₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by sorry
