-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/d542342c-626a-56f1-a421-62ffe8c586fe
-- title:
--   Base change sends r_Φ into the degree-zero η-piece
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota$ a ring homomorphism from $\mathrm{Zp2}\,p=W(\mathbb{F}_{p^2})$ to $W(k)$. Let $\Phi$ be a formal $O_D$-module over $W(k)/pW(k)$ (a commutative two-dimensional formal group law with a $W(\mathbb{F}_{p^2})$-action and an endomorphism $\varpi$ with $\varpi^2=[p]$, $\varpi\circ a=\sigma(a)\circ\varpi$). Assume: $\Phi$ is special for the reduction $j=\mathrm{mk}\circ\iota$ (its tangent space splits into the $j$- and $\sigma j$-eigenparts, each an invertible module); $\Phi$ has height $4$, i.e. the kernel of multiplication by $p$ has degree $p^4$; $\Phi.\mathrm{lieZero}\ j\le\ker\Phi.\mathrm{lieVarpi}$; and $\mathrm{hc}\Phi$, that the graded pieces in degrees $0$ and $1$ of the Cartier module $\mathrm{CartierModule}\ p\ \Phi.F$ (defined by $a\cdot f=j(a)^{p^n}f$ for Teichmüller units $a$) are complementary, so that $\Phi$ yields graded Cartier module data $D_\Phi$. Let $r_\Phi:\mathbb{Z}_p^2\to D_\Phi.\mathrm{NMod}$ be additive and assume $\mathrm{hr}\Phi$: for every canonical $L$-map $L$ on $D_\Phi$, $r_\Phi$ maps the whole of $\mathbb{Z}_p^2$ bijectively onto $D_\Phi.\mathrm{etaPiece}\ L\ 0$ (the degree-zero part of $\eta(L)$). Let $K$ be an algebraically closed field of characteristic $p$ which is a $\mathbb{Z}_p$-algebra, $\psi':W(k)\to K$ a ring homomorphism, with $p$ nilpotent in $K$, and let $t'$ be a rigidified object (a formal $O_D$-module over $K$ together with $n\in\mathbb{N}$ and a power-series datum $\rho$ over $K/pK$) which is admissible for $\iota,\psi'$, i.e. $t'.X$ is special of height $4$ and $\rho$ is an isogeny of height $4n$ from $\Phi$ pushed to $K/pK$ to $t'.\mathrm{Xbar}$. Work over the localisation of $K$ away from $1$, via $\mathrm{awayHom}\ (1:K)$, and assume the degree-$0$/degree-$1$ complementarity hypotheses $\mathrm{IsGradedS}$, $\mathrm{IsGradedSbar}$ and $\mathrm{IsGradedPhiS}$ there, together with a canonical $L$-map $L'$ on the graded data attached to $t'.\mathrm{XS}$. The conclusion: for every canonical $L$-map $L_\Phi$ on the graded Cartier module data of $\mathrm{PhibarS}\ \psi'$ over the localisation, with respect to $\mathrm{jPhiS}$, and every $w\in\mathbb{Z}_p^2$, the image of $r_\Phi(w)$ under the map $\mathrm{nMap}$ on $N$-modules induced by the base-change homomorphism $\mathrm{bcPhi}$ on Cartier modules (which commutes with Verschiebung and with $\varpi$) lies in $\mathrm{etaPiece}\ L_\Phi\ 0$, the intersection of $\eta(L_\Phi)$ with the degree-zero piece.
--
--   This is the naturality, under base change along $W(k)\to K$ followed by localisation, of the $\eta$-lattice attached to a canonical $L$-map in the Cartier-theoretic description of special formal $O_D$-modules: the rigidifying lattice $r_\Phi(\mathbb{Z}_p^2)$ of the base point is carried into the degree-zero $\eta$-piece downstairs. It feeds the subsequent determinant computations for rigid numerators and the comparison of $\eta$-pieces across base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ' : WittVector p k →+* K) (hK : IsNilpotent (p : K))
    (t' : Rigidified p Φ K) (ht' : t'.IsAdmissible ι ψ')
    (hc : t'.IsGradedS ι ψ' (Rigidified.awayHom (1 : K))) (hcb : t'.IsGradedSbar ι ψ' (Rigidified.awayHom (1 : K)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' (Rigidified.awayHom (1 : K)))
    (L' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).M →+
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod)
    (hL' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsCanonicalLMap L') :
    ∀ (LΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).M →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod) (hLΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).IsCanonicalLMap LΦ)
      (w : Fin 2 → ℤ_[p]), (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (rΦ w) ∈ (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0) := by sorry
