-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_isIsomorphic_of_line_transport_of_not_node
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.isIsomorphic_of_line_transport_of_not_node
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/b1baf533-74ec-50bc-8f2e-81762758e4e8
-- title:
--   Line transport determines first-order deformations at a smooth point
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota \colon \mathbb{W}(\mathbb{F}_{p^2}) \to \mathbb{W}(k)$, and let $\Phi$ be a formal $O_D$-module over $\mathbb{W}(k)/p$ which is special for the induced map $\bar\jmath = \iota \bmod p$ (its zero and one Lie eigenspaces are complementary and invertible), has height $4$, and satisfies $\mathrm{lieVarpi}\,m = 0$ for all $m$ in its zero eigenspace; assume the graded pieces $0$ and $1$ of the Cartier module of $\Phi$ are complementary, giving graded Cartier module data, and let $r_\Phi \colon (\mathbb{Z}_p)^2 \to \mathrm{NMod}$ be an additive map which, for every canonical $L$-map $L$, is a bijection of its whole domain onto the $\eta$-piece of $L$ in degree $0$. Let $\kappa$ be an algebraically closed $\mathbb{Z}_p$-algebra field, $\psi_R \colon \mathbb{W}(k) \to \kappa[\varepsilon]$ a ring homomorphism with $p$ nilpotent in $\kappa[\varepsilon]$, and $t, t'$ rigidified objects over $\kappa[\varepsilon]$ (a formal $O_D$-module $X$, an integer $n$, a series $\rho$ modulo $p$) which are admissible for $\iota, \psi_R$: $X$ special, of height $4$, and $\rho$ an isogeny $\bar\Phi \to \bar X$ of height $4n$. Let $Q, Q'$ be Drinfeld data over $\kappa[\varepsilon]$ for $(\mathbb{Q}_p, p)$ together with $\kappa[\varepsilon]$-linear isomorphisms $\sigma_0, \sigma_1$ of $Q.T_0, Q.T_1$ with the Lie eigenspaces of $t.X$, and $\sigma_0', \sigma_1'$ likewise for $t'$, such that $t$ is a Cartier quadruple via $(\iota, h_{c\Phi}, r_\Phi, \psi_R, Q, \sigma_0, \sigma_1)$ and $t'$ one via $(Q', \sigma_0', \sigma_1')$. Let $\Lambda \colon \mathrm{Lie}\,t.X \to \mathrm{Lie}\,t'.X$ be a $\kappa[\varepsilon]$-linear isomorphism, and let $\psi_\kappa$ be the composite of $\psi_R$ with $\kappa[\varepsilon] \to \kappa$. Assume: (smoothness) it is not the case that both Lie eigenspaces of the reduction $t \bmod \varepsilon$ are annihilated by $\mathrm{lieVarpi}$; (reduced isomorphism) series $u_0, v_0$ over $\kappa$ and $m \in \mathbb{N}$ which are mutually inverse $O_D$-homomorphisms between the reductions of $t$ and $t'$ modulo $\varepsilon$ and satisfy the rigidification identity $\mathrm{act}(p^{m+n'}) \circ (\bar u_0 \circ \rho) = \mathrm{act}(p^{m+n}) \circ \rho'$ there; (compatibility of $\Lambda$) $\Lambda$ carries each Lie eigenspace of $t.X$ onto the corresponding one of $t'.X$, commutes with $\mathrm{lieVarpi}$, and reduces modulo $\varepsilon$ to the linear part of $u_0$; (equal lattices) $Q.N_0 = Q'.N_0$ and $Q.N_1 = Q'.N_1$ at every prime; and (line transport) for every prime $x$ of $\kappa[\varepsilon]$, every index $i$ and every $v \in \mathbb{Q}_p^2$, whenever $f \notin x$ together with the graded splitting hypotheses for $t$ away from $f$, a canonical $L$-map $L$, an $\eta$-section $z$ of index $i$ over $v$, and a Cartier module element whose class modulo the Verschiebung range is the $u$-image of $z$ are given, and likewise $f', L', z'$ and an element for $t'$, then the images in the local ring at $x$ of the tangent coordinates of the primed element are obtained from those of the unprimed one by the matrix of $\Lambda$ on the standard basis. The conclusion is that $t$ and $t'$ are isomorphic as rigidified objects over $\kappa[\varepsilon]$: there are mutually inverse $O_D$-homomorphisms $u, v$ between $t.X$ and $t'.X$ and an integer $m$ with $\mathrm{act}(p^{m+t'.n}) \circ (\bar u \circ t.\rho) = \mathrm{act}(p^{m+t.n}) \circ t'.\rho$.
--
--   This is the first-order ($\kappa[\varepsilon]$-level) rigidity step in the Čerednik–Drinfeld comparison: at a smooth point of the special fibre the deformation class of an admissible rigidified special formal $O_D$-module is recovered from the position of the line spanned by the tangent vector of an $\eta$-section inside the invertible Lie eigenspace, so a graded, $\Pi$-equivariant transport $\Lambda$ of those lines lifts the isomorphism of reductions to an isomorphism over $\kappa[\varepsilon]$. It is used in the deduction that rigidified objects with isomorphic associated Drinfeld data are isomorphic over rings in which $p$ is nilpotent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_isIsomorphic_of_line_transport_of_not_node.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.isIsomorphic_of_line_transport_of_not_node
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
    (ψκ : WittVector p k →+* κ) (hresψ : (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).comp ψR = ψκ)

    (hsmooth : ¬ ((∀ w ∈ (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieZero (structureMap ι ψκ), (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieVarpi w = 0) ∧
        (∀ w ∈ (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieOne (structureMap ι ψκ), (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieVarpi w = 0)))

    (u₀ v₀ : Series κ) (m : ℕ)
    (hu₀ : FormalODModule.IsODHom (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X u₀) (hv₀ : FormalODModule.IsODHom (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X v₀)
    (hvu : v₀.comp u₀ = Series.id κ) (huv : u₀.comp v₀ = Series.id κ)
    (hρ : ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp ((u₀.map (Ideal.Quotient.mk (pIdeal p κ))).comp (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ)
      = ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ)

    (hΛ0 : Submodule.map Λ.toLinearMap (t.X.lieZero (structureMap ι ψR)) = t'.X.lieZero (structureMap ι ψR))
    (hΛ1 : Submodule.map Λ.toLinearMap (t.X.lieOne (structureMap ι ψR)) = t'.X.lieOne (structureMap ι ψR))
    (hΛPi : ∀ w : t.X.Lie, Λ (t.X.lieVarpi w) = t'.X.lieVarpi (Λ w))
    (hΛred : ∀ (w : t.X.Lie) (i : Fin 2), TrivSqZeroExt.fst (Λ w i) =
      (Matrix.mulVecLin (MvFormalGroup.linearPart u₀) (fun j => TrivSqZeroExt.fst (w j))) i)

    (hN : ∀ x, Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x)
    (hline : ∀ (x : PrimeSpectrum (DualNumber κ)) (i : Fin 2) (v : Fin 2 → ℚ_[p])
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
          ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').u L' hL'.isCartierLMap.map_verschiebung ⟨z', (AddSubgroup.mem_inf.mp hz'.1).1⟩),
        ∀ j : Fin 2, Rigidified.awayToLoc x f' hf' (MvFormalGroup.CartierModule.tangent m' j) =
        ∑ l : Fin 2, Rigidified.locHom x (Λ (Pi.single l 1) j) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m l)) :
    t.IsIsomorphic t' := by sorry
