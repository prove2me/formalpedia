-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_awayToLoc_tangent_eq_sum_of_iso
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.awayToLoc_tangent_eq_sum_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/0a07fc31-81a6-5dfb-815a-23bfafa76e29
-- title:
--   Tangent germs transported by a Cartier quadruple isomorphism
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring map $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to W(k)$, and a formal $O_D$-module $\Phi$ over $W(k)/pW(k)$ which is special for the reduction $\bar\iota$ of $\iota$ (its Lie subspaces `lieZero` and `lieOne` are complementary and invertible), has height $4$, satisfies $\mathrm{lieVarpi}(m)=0$ for all $m$ in `lieZero`, and whose Cartier module has complementary graded pieces in degrees $0$ and $1$ (hypothesis $h_{c\Phi}$); let $r_\Phi : (\mathrm{Fin}\,2 \to \mathbb{Z}_p) \to_+ N$ be an additive map into the $N$-module of the associated graded Cartier module data which, for every canonical $L$-map $L$, is a bijection from the whole source onto the degree-$0$ $\eta$-piece of $L$. Let $\kappa$ be an algebraically closed $\mathbb{Z}_p$-algebra field, $\psi_R : W(k) \to \kappa[\varepsilon]$ a ring map with $p$ nilpotent in $\kappa[\varepsilon]$, and $t,t'$ rigidified data over $\kappa[\varepsilon]$ (a formal $O_D$-module $X$, an integer $n$, a series $\rho$) that are admissible for $(\iota,\psi_R)$: $X$ special, of height $4$, and $\rho$ an isogeny of height $4n$ from $\bar\Phi$ to $\bar X$. Let $Q,Q'$ be Drinfeld data over $\kappa[\varepsilon]$ for the uniformiser $p \in \mathbb{Z}_p \subset \mathbb{Q}_p$, with $\kappa[\varepsilon]$-linear identifications $\sigma_0 : Q.T_0 \cong \mathrm{lieZero}(t.X)$, $\sigma_1 : Q.T_1 \cong \mathrm{lieOne}(t.X)$ and likewise $\sigma_0',\sigma_1'$ for $t'$, such that `IsCartierQuadrupleVia` holds in both cases: $\rho$ is an $O_D$-module homomorphism $\bar\Phi \to \bar X$, the identifications intertwine $Q.\Pi_0, Q.\Pi_1$ with `lieVarpi` on $\mathrm{Lie}\,X$, and at every prime $x$ the lattices $N_0 x, N_1 x$ consist exactly of those $v$ admitting an $\eta$-section datum of index $0$ resp. $1$ over some $\kappa[\varepsilon]_f$ with $f \notin x$, the maps $u_0, u_1$ computing the corresponding tangent vectors through $\sigma_0,\sigma_1$ up to a unit. Assume further an isomorphism $I : Q \cong Q'$ of Drinfeld data and a $\kappa[\varepsilon]$-linear isomorphism $\Lambda : \mathrm{Lie}\,t.X \cong \mathrm{Lie}\,t'.X$ (both equal to $(\mathrm{Fin}\,2 \to \kappa[\varepsilon])$) with $\Lambda \circ \sigma_0 = \sigma_0' \circ I.\tau_0$ and $\Lambda \circ \sigma_1 = \sigma_1' \circ I.\tau_1$ as maps into $\mathrm{Lie}$. Finally fix a prime $x$ of $\kappa[\varepsilon]$, an index $i \in \mathrm{Fin}\,2$, a vector $v : \mathrm{Fin}\,2 \to \mathbb{Q}_p$, and presentations on both sides: $f \notin x$ with complementarity of the graded pieces for $t.X$, for its reduction and for $\bar\Phi$ over the localisation away from $f$, a canonical $L$-map $L$, an element $z$ satisfying `IsEtaSection` of index $i$ for $v$, and $m$ in the Cartier module whose class modulo the image of Verschiebung equals $u\,L$ applied to the $\eta$-part of $z$; and correspondingly $f', L', z', m'$ for $t'$ with the same $i$ and the same $v$. Then for every $j \in \mathrm{Fin}\,2$, the image of the $j$-th tangent coordinate of $m'$ in the local ring of $\kappa[\varepsilon]$ at $x$ equals $\sum_{l} \Lambda_{jl}\,$ times the image of the $l$-th tangent coordinate of $m$, where $\Lambda_{jl}$ denotes the $j$-th coordinate of $\Lambda$ applied to the $l$-th standard basis vector, mapped into the local ring.
--
--   This is the transport half of the rigidity argument of Boutot–Carayol II (11.9): an isomorphism of the Drinfeld data attached to two admissible rigidified formal $O_D$-modules over the dual numbers forces the tangent germs produced by the $\eta$-section presentations to be related by the single linear map $\Lambda$, independently of the chosen presentations $(f,L,z,m)$. It feeds the deduction that two such rigidified objects with isomorphic Cartier quadruples over $\kappa[\varepsilon]$ are themselves isomorphic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_awayToLoc_tangent_eq_sum_of_iso.lean

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

open scoped TensorProduct

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.awayToLoc_tangent_eq_sum_of_iso
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra ℤ_[p] κ]
    (ψR : WittVector p k →+* DualNumber κ) (hR : IsNilpotent (p : DualNumber κ))
    (t t' : Rigidified p Φ (DualNumber κ)) (ht : t.IsAdmissible ι ψR) (ht' : t'.IsAdmissible ι ψR)
    (Q Q' : FormalOmega.DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) (DualNumber κ))
    (σ₀ : Q.T₀ ≃ₗ[DualNumber κ] ↥(t.X.lieZero (structureMap ι ψR)))
    (σ₁ : Q.T₁ ≃ₗ[DualNumber κ] ↥(t.X.lieOne (structureMap ι ψR)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψR Q σ₀ σ₁)
    (σ₀' : Q'.T₀ ≃ₗ[DualNumber κ] ↥(t'.X.lieZero (structureMap ι ψR)))
    (σ₁' : Q'.T₁ ≃ₗ[DualNumber κ] ↥(t'.X.lieOne (structureMap ι ψR)))
    (hQ' : t'.IsCartierQuadrupleVia ι hcΦ rΦ ψR Q' σ₀' σ₁')
    (Λ : t.X.Lie ≃ₗ[DualNumber κ] t'.X.Lie)
    (I : Q.Iso Q')
    (hΛ₀ : ∀ s : Q.T₀, Λ ((σ₀ s : ↥(t.X.lieZero (structureMap ι ψR))) : t.X.Lie) =
      ((σ₀' (I.τ₀ s) : ↥(t'.X.lieZero (structureMap ι ψR))) : t'.X.Lie))
    (hΛ₁ : ∀ s : Q.T₁, Λ ((σ₁ s : ↥(t.X.lieOne (structureMap ι ψR))) : t.X.Lie) =
      ((σ₁' (I.τ₁ s) : ↥(t'.X.lieOne (structureMap ι ψR))) : t'.X.Lie))
    (x : PrimeSpectrum (DualNumber κ)) (i : Fin 2) (v : Fin 2 → ℚ_[p])
    (f : DualNumber κ) (hf : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψR (Rigidified.awayHom f))
    (hcb : t.IsGradedSbar ι ψR (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψR (Rigidified.awayHom f))
    (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
    (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψR ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v)
    (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).M)
    (hm : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).vRange.mkQ m =
      ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩)
    (f' : DualNumber κ) (hf' : f' ∉ x.asIdeal) (hc' : t'.IsGradedS ι ψR (Rigidified.awayHom f'))
    (hcb' : t'.IsGradedSbar ι ψR (Rigidified.awayHom f')) (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψR (Rigidified.awayHom f'))
    (L' : _) (hL' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').IsCanonicalLMap L')
    (z' : _) (hz' : t'.IsEtaSection ι hcΦ rΦ ψR ht'.2.2.1 (Rigidified.awayHom f') hc' hcb' hcΦf' L' hL' i z' v)
    (m' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').M)
    (hm' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').vRange.mkQ m' =
      ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').u L' hL'.isCartierLMap.map_verschiebung ⟨z', (AddSubgroup.mem_inf.mp hz'.1).1⟩) :
    ∀ j : Fin 2, Rigidified.awayToLoc x f' hf' (MvFormalGroup.CartierModule.tangent m' j) =
        ∑ l : Fin 2, Rigidified.locHom x (Λ (Pi.single l 1) j) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m l) := by sorry
