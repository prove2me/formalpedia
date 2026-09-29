-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/9412315a-d3e4-52c7-82fb-5467b55bd8bb
-- title:
--   Isomorphic Cartier quadruples force isomorphic rigidified special modules
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, and a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and write $\bar\jmath$ for $\iota$ followed by the quotient map $W(k)\to W(k)/pW(k)$. Let $\Phi$ be a formal $\mathcal O_D$-module over $W(k)/pW(k)$, i.e. a $2$-dimensional formal group law with a $W(\mathbb F_{p^2})$-action and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ a=\sigma(a)\circ\varpi$, subject to: `hΦ`, $\Phi$ is special for $\bar\jmath$, meaning $\mathrm{Lie}\,\Phi$ is the direct sum of the two eigenspaces $\mathrm{lieZero}$, $\mathrm{lieOne}$ of the $W(\mathbb F_{p^2})$-action, each an invertible module; `hΦ4`, the kernel of $[p]$ on $\Phi$ is finite projective of degree $p^4$ in every field fibre; `h0Φ`, the eigenspace $\mathrm{lieZero}$ is contained in the kernel of the linear part of $\varpi$ on $\mathrm{Lie}\,\Phi$; `hcΦ`, the graded pieces of index $0$ and $1$ of the Cartier module of $\Phi$ (elements on which the Teichmüller action of $c\in\mathbb F_{p^2}$ agrees with homothety by $\bar\jmath(\tau(c))^{p^n}$, $n=0,1$) are complementary; and an additive map $r_\Phi\colon\mathbb Z_p^2\to N$ into the $N$-module of the associated graded Cartier module data which, by `hrΦ`, maps $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\mathrm{etaPiece}\,L\,0$ for every canonical $L$-map $L$. Let further $\kappa$ be an algebraically closed $\mathbb Z_p$-algebra which is a field in which $p$ is nilpotent, $\psi\colon W(k)\to\kappa$ a ring homomorphism, and $t=(X,n,\rho)$, $t'=(X',n',\rho')$ rigidified data over $\kappa$ (a formal $\mathcal O_D$-module, a natural number, and a system of power series over $\kappa/p\kappa$) which are admissible for $(\iota,\psi)$: $X$ is special and of height $4$, and $\rho$ is an isogeny $\bar\Phi_\psi\to\bar X$ of height $4n$. Finally let $Q,Q'$ be Drinfeld data over $\kappa$ for $K=\mathbb Q_p$ with uniformiser $p\in\mathbb Z_p$, assume $Q$ is a Cartier quadruple for $t$ and $Q'$ one for $t'$ (with respect to $\iota$, $\mathrm{hc}_\Phi$, $r_\Phi$, $\psi$), and assume $Q$ and $Q'$ are isomorphic. Then $t$ and $t'$ are isomorphic: there are power-series systems $u,v$ over $\kappa$ and an $m\in\mathbb N$ such that $u\colon X\to X'$ and $v\colon X'\to X$ are mutually inverse homomorphisms of formal $\mathcal O_D$-modules and $[p^{m+n'}]\circ(\bar u\circ\rho)=[p^{m+n}]\circ\rho'$ on $\bar X'$.
--
--   This is the injectivity half of Drinfeld's classification of special formal $\mathcal O_D$-modules with rigidification in terms of lattice data, as in Boutot–Carayol, chapter II: over an algebraically closed base the Cartier module recovers the formal module, so an isomorphism of the associated Drinfeld data lifts to an isomorphism of the rigidified objects. It is used in the proof that the period map is bijective on geometric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {κ : Type} [Field κ] [IsAlgClosed κ] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (hκ : IsNilpotent (p : κ))
    (t t' : Rigidified p Φ κ) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ ψ Q')
    (hiso : Q.IsIsomorphic Q') :
    t.IsIsomorphic t' := by sorry
