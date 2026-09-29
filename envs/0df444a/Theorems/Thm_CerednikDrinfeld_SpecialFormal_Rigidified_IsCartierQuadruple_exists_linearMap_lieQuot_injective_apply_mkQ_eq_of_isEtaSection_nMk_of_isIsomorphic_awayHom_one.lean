-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/bb71e735-9b1e-5c0d-a7b5-20952f3e201c
-- title:
--   Isomorphic Cartier quadruples induce an injection of Lie quotients
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring map $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ over $W(k)/pW(k)$ whose degree-$0$ and degree-$1$ graded pieces of its Cartier module, taken with respect to the reduction $\bar\iota$ of $\iota$, are complementary (hypothesis $h_{c\Phi}$), together with an additive map $r_\Phi : \mathbb{Z}_p^2 \to N$ into the $N$-module of the associated graded Cartier module data of $\Phi$. Let $\kappa$ be a field of characteristic $p$ which is a $\mathbb{Z}_p$-algebra, $\psi : W(k) \to \kappa$ a ring map, and let $t = (X,n,\rho)$ and $t' = (X',n',\rho')$ be rigidified objects over $\kappa$ that are admissible for $(\iota,\psi)$, i.e. $X$ is special of height $4$ and $\rho$ is an isogeny of height $4n$ from $\bar\Phi$ to $\bar X$, and likewise for $t'$. Let $Q,Q'$ be Drinfeld data over $\kappa$ for the uniformiser $p \in \mathbb{Z}_p$ inside $\mathbb{Q}_p$, assume $t$ realises $Q$ and $t'$ realises $Q'$ as Cartier quadruples, and assume $Q$ and $Q'$ are isomorphic. Assume further that $\rho$, resp. $\rho'$, is a homomorphism of formal $\mathcal{O}_D$-modules $\bar\Phi \to \bar X$, resp. $\bar\Phi \to \bar X'$, that for the structure map $\kappa \to \kappa[1^{-1}]$ the degree-$0$ and degree-$1$ graded pieces are complementary for the base-changed modules $X_S$, $\bar X_S$, $X'_S$, $\bar X'_S$ and for $\bar\Phi_S$, and let $L$, $L'$ be canonical $L$-maps $M \to N$, $M' \to N'$ for the resulting graded Cartier module data $D$, $D'$. The conclusion asserts the existence of a $W(\kappa[1^{-1}])$-linear map $\tau : M/VM \to M'/VM'$ between the Lie quotients (the quotients by the images of the Verschiebungs) which is injective and has the following compatibility: for every $i \in \{0,1\}$, every $m \in M$, $m' \in M'$ and every $v \in \mathbb{Q}_p^2$, if the class of $(m,0)$ in $N$ is an $\eta$-section of $t$ in degree $i$ with coordinates $v$ — that is, it lies in the degree-$i$ $\eta$-piece cut out by $L$, and the reduction along $\bar X_S$ of its $i$-th $\varpi$-power satisfies the lattice relation with respect to the rigidified numbering built from $r_\Phi$ and level $n$ at the vector $p^i v$ — and the class of $(m',0)$ in $N'$ is such an $\eta$-section of $t'$ in the same degree $i$ with the same $v$, then $\tau$ sends the class of $m$ in $M/VM$ to the class of $m'$ in $M'/VM'$.
--
--   This is the step asserting that the Drinfeld datum determines the position of $VM$ inside the Cartier module, in the form comparing two rigidified special formal $\mathcal{O}_D$-modules over a field whose Cartier quadruples are isomorphic: $\eta$-sections with equal $\mathbb{Q}_p^2$-coordinates are matched by a single injective map of Lie quotients, obtained from the tangent description of $M/VM$ in characteristic $p$ and the isomorphism of Lie algebras glued from the two graded pieces. It feeds the statement that the resulting map on $\eta$-pieces is bijective on critical sections, in the Čerednik–Drinfeld uniformisation part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t t' : Rigidified p Φ κ) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ ψ Q')
    (hiso : Q.IsIsomorphic Q')
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ) (hOD' : FormalODModule.IsODHom (t'.Φbar ψ) t'.Xbar t'.ρ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hc' : t'.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb' : t'.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : κ)))
    (L : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) (hL : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).IsCanonicalLMap L)
    (L' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) (hL' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').IsCanonicalLMap L') :
    ∃ τ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).LieQuot →ₗ[WittVector p (Rigidified.Baway (1 : κ))] ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').LieQuot,
      Function.Injective τ ∧
      ∀ (i : Fin 2) (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (m' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M) (v : Fin 2 → ℚ_[p]),
        t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0)) v →
        t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i (((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (m', 0)) v →
        τ (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).vRange.mkQ m) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').vRange.mkQ m' := by sorry
