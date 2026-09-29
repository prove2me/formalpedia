-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_isCritical_addMonoidHom_etaPiece_bijective_isEtaSection_iff_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_isCritical_addMonoidHom_etaPiece_bijective_isEtaSection_iff_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/ac859b5a-2030-507a-89aa-7bd4c47a6ab5
-- title:
--   Isomorphic Cartier quadruples: a common critical index and η-sections
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and let $\Phi$ be a formal $\mathcal O_D$-module over $W(k)/p$ for the structure map $\bar\jmath$ obtained from $\iota$ by reduction. Assume: $\Phi$ is special for $\bar\jmath$ (its Lie pieces $\mathrm{Lie}_0$ and $\mathrm{Lie}_1$ are complementary and invertible), $\Phi$ has height $4$, $\mathrm{Lie}_0\Phi\subseteq\ker\mathrm{Lie}(\varpi)$, the graded pieces $0$ and $1$ of the Cartier module of $\Phi$ are complementary (hypothesis `hcΦ`), $r_\Phi$ is an additive map from $\mathbb Z_p^2$ to the module `NMod` of the associated graded Cartier module data, a canonical $L$-map for $\Phi$ exists, and for every canonical $L$-map $L$ the map $r_\Phi$ carries the whole of $\mathbb Z_p^2$ bijectively onto `etaPiece L … 0`. Let $\kappa$ be an algebraically closed field of characteristic $p$ that is a $\mathbb Z_p$-algebra, $\psi\colon W(k)\to\kappa$ a ring homomorphism, and $t=(X,n,\rho)$, $t'=(X',n',\rho')$ rigidified triples over $\kappa$ that are admissible for $(\iota,\psi)$ (special, of height $4$, with $\rho$ an isogeny of height $4n$). Let $Q,Q'$ be Drinfeld data over $\kappa$ for $\pi=p\in\mathbb Z_p$, $K=\mathbb Q_p$, such that $t$ is a Cartier quadruple for $Q$ and $t'$ for $Q'$, and assume $Q$ and $Q'$ are isomorphic. Assume further that $\rho$ and $\rho'$ are $\mathcal O_D$-homomorphisms $\bar\Phi\to\bar X$ respectively $\bar\Phi\to\bar X'$, that the gradings of $X$, $\bar X$, $X'$, $\bar X'$ and of $\bar\Phi$ are complementary after base change along the localisation $\kappa\to\kappa[1^{-1}]$, and that $L$, $L'$ are canonical $L$-maps for the graded Cartier module data of $X$ and $X'$ over $\kappa[1^{-1}]$. Then there is an index $i\in\{0,1\}$ with the following three properties: every $m$ in the $i$-th graded piece of the Cartier module of $X_{\kappa[1^{-1}]}$ satisfies $\varpi\cdot m=Vy$ for some $y$, and likewise for $X'_{\kappa[1^{-1}]}$; and there exist an additive homomorphism $\theta_\eta$ from `etaPiece L … i` to `etaPiece L' … i` and a $W(\kappa[1^{-1}])$-linear map $\tau$ from $M/VM$ to $M'/VM'$ such that $\theta_\eta$ is bijective, $\tau$ is injective, whenever $m\in M$, $m'\in M'$ are such that the class of $(m,0)$ lies in `etaPiece L … i` and $\theta_\eta$ sends it to the class of $(m',0)$ one has $\tau([m])=[m']$, and for all $z\in$ `etaPiece L … i` and all $v\in\mathbb Q_p^2$ the relation `IsEtaSection` holds for $t$ at $i$ with $z$ and $v$ if and only if it holds for $t'$ at $i$ with $\theta_\eta z$ and the same $v$.
--
--   This is the transfer statement behind the Čerednik–Drinfeld reconstruction step: an isomorphism of the Drinfeld data attached to two admissible rigidified special formal $\mathcal O_D$-modules over an algebraically closed field yields a single index critical for both, together with a coordinate-preserving bijection of $\eta$-sections and an injective map of Lie quotients. It feeds the comparison of the underlying Cartier modules themselves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_isCritical_addMonoidHom_etaPiece_bijective_isEtaSection_iff_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_isCritical_addMonoidHom_etaPiece_bijective_isEtaSection_iff_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {κ : Type} [Field κ] [IsAlgClosed κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
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
    ∃ i : Fin 2,
      (∀ m ∈ (t.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F,
          MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd m) ∧
      (∀ m ∈ (t'.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom (1 : κ))).F,
          MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t'.XS (Rigidified.awayHom (1 : κ))).varpiEnd m) ∧
      ∃ (θη : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
        (τ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).LieQuot →ₗ[WittVector p (Rigidified.Baway (1 : κ))] ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').LieQuot),
        Function.Bijective θη ∧ Function.Injective τ ∧
        (∀ (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (m' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M) (hm : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0) ∈ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
            ((θη ⟨((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0), hm⟩ : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) =
              ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (m', 0) →
            τ (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).vRange.mkQ m) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').vRange.mkQ m') ∧
        (∀ (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i) (v : Fin 2 → ℚ_[p]),
            t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i (z : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) v ↔
              t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i ((θη z : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) v) := by sorry
