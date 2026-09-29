-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_mem_etaPiece_tangent_eq_of_line_transport
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_mem_etaPiece_tangent_eq_of_line_transport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/6760ce1d-0f2b-598a-b45b-ad408c53fcf6
-- title:
--   Transport of ηᵢ-sections along Λ with prescribed tangent vector
-- statement:
--   The setting is that of special formal $\mathcal{O}_D$-modules over the dual numbers. Fixed data: a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : \mathbb{W}(k)_{(2)} \to W(k)$ from the Witt vectors of the field with $p^2$ elements, and a formal $\mathcal{O}_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$, the structure map used throughout being $\bar\jmath = \iota$ followed by the reduction $W(k) \to W(k)/pW(k)$.
--
--   Hypotheses on $\Phi$: `hΦ` says $\Phi$ is special for $\bar\jmath$, that is, $\operatorname{Lie}\Phi$ is the direct sum of the eigen-submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$ (kernels of $\mathrm{lieAct}(a) - \bar\jmath(a)$ resp. $\mathrm{lieAct}(a) - \bar\jmath(\sigma a)$, intersected over $a$), both invertible; `hΦ4` says $\Phi$ has height $4$, i.e. the action of $p$ has kernel of degree $p^4$; `h0` says $\mathrm{lieVarpi}$, the linear part of the action of the uniformiser, vanishes on $\mathrm{lieZero}$; `hcΦ` says the graded pieces of index $0$ and $1$ of the Cartier module of $\Phi$ are complementary, so that the graded Cartier module data $D_\Phi$ of $\Phi$ are defined; $r_\Phi$ is an additive map $(\mathbb{Z}_p)^2 \to (D_\Phi).\mathrm{NMod}$, and `hrΦ` requires that for every canonical $L$-map $L$ on $D_\Phi$, $r_\Phi$ is a bijection from the whole of $(\mathbb{Z}_p)^2$ onto the degree-$0$ $\eta$-piece $\mathrm{etaPiece}\,L\,\_\,0 = \mathrm{eta}(L) \cap \mathrm{nPiece}\,0$.
--
--   Base data: an algebraically closed field $\kappa$ which is a $\mathbb{Z}_p$-algebra, a ring homomorphism $\psi_R : W(k) \to \kappa[\varepsilon]$ into the dual numbers, and `hR`: $p$ is nilpotent in $\kappa[\varepsilon]$. Two rigidified objects $t, t'$ over $\kappa[\varepsilon]$ (each consisting of a formal $\mathcal{O}_D$-module $X$, an integer $n$, and a series $\rho$ over $\kappa[\varepsilon]/p$) are given, both admissible for $(\iota,\psi_R)$ by `ht`, `ht'`: $X$ is special for the structure map $\psi_R \circ \iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from $\bar\Phi$ to $\bar X$.
--
--   Drinfeld data: $Q, Q'$ are Drinfeld data over $\kappa[\varepsilon]$ for $\mathbb{Q}_p$ and the uniformiser $p \in \mathbb{Z}_p$ (pairs of full lattices $N_0 \subseteq N_1$ in $\mathbb{Q}_p^2$ depending on the point of $\operatorname{Spec}\kappa[\varepsilon]$ with $pN_1 \subseteq N_0$ and the membership sets open, invertible modules $T_0, T_1$ with maps $\Pi_0, \Pi_1$ whose composites are multiplication by $p$, and comparison maps $u_0, u_1$ from the base-changed lattices to the stalks of $T_0, T_1$, compatible with inclusion and with $\Pi_0$). The isomorphisms $\sigma_0 : Q.T_0 \cong \mathrm{lieZero}(t.X)$, $\sigma_1 : Q.T_1 \cong \mathrm{lieOne}(t.X)$ and their primed analogues $\sigma_0', \sigma_1'$ for $t'$ are $\kappa[\varepsilon]$-linear. The hypotheses `hQ` and `hQ'` assert $t.\mathrm{IsCartierQuadrupleVia}$ and $t'.\mathrm{IsCartierQuadrupleVia}$ for these data: $\rho$ is an $\mathcal{O}_D$-module homomorphism $\bar\Phi \to \bar X$; $\sigma_1 \circ \Pi_0 = \mathrm{lieVarpi} \circ \sigma_0$ and $\sigma_0 \circ \Pi_1 = \mathrm{lieVarpi} \circ \sigma_1$; and (further clauses, summarised here) at every point $x$ the lattice $N_0 x$, resp. $N_1 x$, consists exactly of those $v$ admitting an $\eta$-section of index $0$, resp. $1$, with parameter $v$ over some localisation away from an element $f \notin x$, together with the requirement that $u_0$ and $u_1$ send such $v$, through $\sigma_0$ and $\sigma_1$, to the tangent vectors of Cartier-module lifts of those sections.
--
--   Comparison data: $\Lambda : \operatorname{Lie}(t.X) \cong \operatorname{Lie}(t'.X)$ is a $\kappa[\varepsilon]$-linear isomorphism of $\kappa[\varepsilon]^2$; $\psi_\kappa : W(k) \to \kappa$ satisfies `hresψ`, namely $\psi_R$ followed by the projection $\kappa[\varepsilon] \to \kappa$, $\varepsilon \mapsto 0$, equals $\psi_\kappa$. Write $\bar t$, $\bar t'$ for the base changes of $t, t'$ along $\varepsilon \mapsto 0$. The hypothesis `hsmooth` is the negation of the conjunction of the two statements that $\mathrm{lieVarpi}$ of $\bar t$ vanishes on $\mathrm{lieZero}(\bar t.X)$ and on $\mathrm{lieOne}(\bar t.X)$ (the excluded configuration being a double point). The reductions are isomorphic in a prescribed way: series $u_0, v_0$ over $\kappa$ and an integer $m$ are given with `hu₀`, `hv₀` stating that $u_0$ is an $\mathcal{O}_D$-module homomorphism $\bar t.X \to \bar t'.X$ and $v_0$ one in the reverse direction, `hvu`, `huv` that $v_0 \circ u_0$ and $u_0 \circ v_0$ are the identity, and `hρ` that the action of $p^{m+\bar t'.n}$ on $\bar t'$ modulo $p$ composed with the reduction of $u_0$ composed with $\bar t.\rho$ equals the action of $p^{m+\bar t.n}$ composed with $\bar t'.\rho$. The compatibilities of $\Lambda$ are: `hΛ0`, `hΛ1` that $\Lambda$ carries $\mathrm{lieZero}(t.X)$ onto $\mathrm{lieZero}(t'.X)$ and $\mathrm{lieOne}(t.X)$ onto $\mathrm{lieOne}(t'.X)$; `hΛPi` that $\Lambda \circ \mathrm{lieVarpi} = \mathrm{lieVarpi} \circ \Lambda$; and `hΛred` that, coordinatewise, the $\varepsilon \mapsto 0$ part of $\Lambda w$ is the image of the $\varepsilon \mapsto 0$ part of $w$ under the matrix of linear coefficients of $u_0$.
--
--   The two remaining hypotheses couple $Q$ and $Q'$. `hN` states $Q.N_0 x = Q'.N_0 x$ and $Q.N_1 x = Q'.N_1 x$ for every $x$. `hline`, the line-transport hypothesis, states: for every point $x$ of $\operatorname{Spec}\kappa[\varepsilon]$, every index $i$, every $v \in \mathbb{Q}_p^2$, every $f \notin x$ together with gradings of the Cartier modules of $t.X$, of its reduction and of $\Phi$ over the localisation away from $f$, every canonical $L$-map $L$ there, every $z$ which is an $\eta$-section of index $i$ with parameter $v$ for $t$ over that localisation, and every $m$ in the Cartier module with $m$ mapping modulo the image of the Verschiebung to $u(L)$ applied to $z$, and likewise for primed data $f', L', z', m'$ attached to $t'$ with the same $i$ and the same $v$: for each $j$, the image of the $j$-th tangent coordinate of $m'$ in the local ring at $x$ equals $\sum_{l} \Lambda(e_l)_j$ times the image of the $l$-th tangent coordinate of $m$, where $e_l$ are the standard basis vectors and the coefficients are taken in the local ring at $x$.
--
--   Finally, $hc$ and $hc'$ are gradings (complementarity of the pieces of index $0$ and $1$) for the Cartier modules of $t.X$ and $t'.X$ over $\kappa[\varepsilon]$ for the structure map $\psi_R \circ \iota$; $\gamma$ is a homogeneous $V$-basis of the Cartier module of $t.X$, i.e. $\gamma_i$ lies in the graded piece of index $i$ and the matrix of tangent vectors of the $\gamma_i$ has unit determinant; $L$ with `hL` and $L'$ with `hL'` are canonical $L$-maps for the graded Cartier module data of $t.X$ and of $t'.X$; and $i \in \{0,1\}$ is an index.
--
--   Conclusion. For every $z$ in the $N$-module of the graded Cartier module data of $t.X$ lying in the $\eta$-piece $\mathrm{etaPiece}\,L\,\_\,i$, and for every element $m$ of the Cartier module of $t.X$ whose class modulo the image of the Verschiebung equals $u(L)$ evaluated at $z$ (using the $\mathrm{eta}$-component of the membership of $z$), there exist an element $z'$ of the $N$-module of the graded Cartier module data of $t'.X$ lying in $\mathrm{etaPiece}\,L'\,\_\,i$ for the same index $i$, and an element $m'$ of the Cartier module of $t'.X$, such that the class of $m'$ modulo the image of the Verschiebung equals $u(L')$ evaluated at $z'$, and the tangent vector of $m'$ equals $\Lambda$ applied to the tangent vector of $m$.
--
--   This is the global form, over the dual numbers $\kappa[\varepsilon]$ and without passing to stalks, of the statement that the line cut out in the tangent space by the $\eta$-sections of a special formal $\mathcal{O}_D$-module is transported by $\Lambda$: every $\eta_i$-section of $t.X$ has a partner $\eta_i$-section of $t'.X$ whose tangent vector is the $\Lambda$-image of its own. It is used in the first-order rigidity argument at a smooth point, where it feeds the construction of an isomorphism between $t$ and $t'$ from the line-transport data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_mem_etaPiece_tangent_eq_of_line_transport.lean

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
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open scoped TensorProduct

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_mem_etaPiece_tangent_eq_of_line_transport
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
        ∑ l : Fin 2, Rigidified.locHom x (Λ (Pi.single l 1) j) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m l))
    (hc : IsCompl (t.X.gradedPiece (structureMap ι ψR) 0) (t.X.gradedPiece (structureMap ι ψR) 1))
    (hc' : IsCompl (t'.X.gradedPiece (structureMap ι ψR) 0) (t'.X.gradedPiece (structureMap ι ψR) 1))
    (γ : Fin 2 → MvFormalGroup.CartierModule p t.X.F) (hγ : t.X.IsHomogeneousVBasis (structureMap ι ψR) γ)
    (L : (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).M →+ (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).NMod) (hL : (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).IsCanonicalLMap L)
    (L' : (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').M →+ (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').NMod) (hL' : (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').IsCanonicalLMap L')
    (i : Fin 2) :
    ∀ (z : (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).NMod) (hz : z ∈ (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).etaPiece L hL.isCartierLMap.map_verschiebung i)
      (m : MvFormalGroup.CartierModule p t.X.F),
      (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).vRange.mkQ m = (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz).1⟩ →
      ∃ (z' : (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').NMod) (hz' : z' ∈ (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
        (m' : MvFormalGroup.CartierModule p t'.X.F),
        (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').vRange.mkQ m' = (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').u L' hL'.isCartierLMap.map_verschiebung ⟨z', (AddSubgroup.mem_inf.mp hz').1⟩ ∧
        MvFormalGroup.CartierModule.tangent m' = Λ (MvFormalGroup.CartierModule.tangent m) := by sorry
