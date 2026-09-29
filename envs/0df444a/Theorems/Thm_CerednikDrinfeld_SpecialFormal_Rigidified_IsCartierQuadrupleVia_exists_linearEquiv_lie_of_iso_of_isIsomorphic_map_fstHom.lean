-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/05e15bf9-b6fb-54f4-8468-8e13a14dc60c
-- title:
--   Lie transport along an isomorphism of Cartier quadruples
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring map $\iota : \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ over $W(k)/pW(k)$ which is special for the reduction $\bar\iota$ of $\iota$ (its Lie module splits as the direct sum of the complementary invertible submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$), has height $4$, and satisfies $\mathrm{lieVarpi}\,m = 0$ for all $m$ in $\mathrm{lieZero}$; assume the graded pieces of index $0$ and $1$ of the Cartier module of $\Phi$ are complementary, witnessed by $hc_\Phi$, and let $r_\Phi : (\mathrm{Fin}\,2 \to \mathbb{Z}_p) \to \mathrm{NMod}$ be an additive map which, for every canonical $L$-map $L$ on the graded Cartier module data of $\Phi$, maps the whole source bijectively onto the $\eta$-piece of index $0$ attached to $L$. Let $\kappa$ be an algebraically closed $\mathbb{Z}_p$-algebra field, $\kappa[\varepsilon]$ its dual numbers, $\psi_R : W(k) \to \kappa[\varepsilon]$ a ring map, and assume $p$ is nilpotent in $\kappa[\varepsilon]$. Let $t = (X, n, \rho)$ and $t' = (X', n', \rho')$ be rigidified objects over $\kappa[\varepsilon]$ that are admissible for $(\iota, \psi_R)$, i.e. $X$ is special of height $4$ for $\psi_R \circ \iota$ and $\rho$ is an isogeny $\bar\Phi \to \bar X$ of height $4n$. Let $Q, Q'$ be Drinfeld data over $\kappa[\varepsilon]$ for $(\mathbb{Z}_p \subset \mathbb{Q}_p, \pi = p)$, let $\sigma_0 : Q.T_0 \cong \mathrm{lieZero}(X)$, $\sigma_1 : Q.T_1 \cong \mathrm{lieOne}(X)$ and $\sigma_0', \sigma_1'$ be the corresponding $\kappa[\varepsilon]$-linear equivalences for $t'$, and assume $Q$ is the Cartier quadruple of $t$ via $(\sigma_0, \sigma_1)$ and $Q'$ that of $t'$ via $(\sigma_0', \sigma_1')$, in the sense of `IsCartierQuadrupleVia` for the data $(\iota, hc_\Phi, r_\Phi, \psi_R)$. Let $I$ be an isomorphism $Q \cong Q'$ of Drinfeld data, with tangent components $I.\tau_0, I.\tau_1$, and assume the reductions of $t$ and $t'$ along $\varepsilon \mapsto 0$ are isomorphic as rigidified objects over $\kappa$. The conclusion provides $u_0, v_0$, each a pair of power series in two variables over $\kappa$, and $m \in \mathbb{N}$, such that $u_0$ is an $\mathcal{O}_D$-homomorphism from the reduction of $X$ to that of $X'$, $v_0$ one in the opposite direction, $v_0 \circ u_0$ and $u_0 \circ v_0$ are the identity, and the rigidifications agree after multiplication by $p^{m+n'}$, respectively $p^{m+n}$, on the reduction modulo $p$ — exactly a witness that the two reductions are isomorphic rigidified objects — together with a $\kappa[\varepsilon]$-linear equivalence $\Lambda : \mathrm{Lie}\,X \cong \mathrm{Lie}\,X'$ satisfying $\Lambda \circ \sigma_0 = \sigma_0' \circ I.\tau_0$ and $\Lambda \circ \sigma_1 = \sigma_1' \circ I.\tau_1$, carrying $\mathrm{lieZero}(X)$ onto $\mathrm{lieZero}(X')$ and $\mathrm{lieOne}(X)$ onto $\mathrm{lieOne}(X')$, commuting with $\mathrm{lieVarpi}$, and whose reduction modulo $\varepsilon$ (coordinatewise first component) is multiplication by the matrix of linear coefficients of $u_0$.
--
--   This is the first-order rigidity step in the Čerednik–Drinfeld comparison between special formal $\mathcal{O}_D$-modules and Drinfeld data: an isomorphism of the associated quadruples over the dual numbers is transported to a graded, $\varpi$-equivariant isomorphism of tangent modules whose reduction is the differential of an isomorphism of the reductions. It is used by `isIsomorphic_of_isCartierQuadruple_of_isIsomorphic_dualNumber_of_isNilpotent`, which upgrades such a tangent-level isomorphism to an isomorphism of the rigidified objects over $\kappa[\varepsilon]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom
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
    (I : Q.Iso Q')
    (hred : (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).IsIsomorphic
      (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ))) :
    ∃ (u₀ v₀ : Series κ) (m : ℕ),

      FormalODModule.IsODHom (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X u₀ ∧
      FormalODModule.IsODHom (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X v₀ ∧
      v₀.comp u₀ = Series.id κ ∧ u₀.comp v₀ = Series.id κ ∧
      ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp ((u₀.map (Ideal.Quotient.mk (pIdeal p κ))).comp (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ)
        = ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ ∧
      ∃ Λ : t.X.Lie ≃ₗ[DualNumber κ] t'.X.Lie,

        (∀ s : Q.T₀, Λ ((σ₀ s : ↥(t.X.lieZero (structureMap ι ψR))) : t.X.Lie) =
          ((σ₀' (I.τ₀ s) : ↥(t'.X.lieZero (structureMap ι ψR))) : t'.X.Lie)) ∧
        (∀ s : Q.T₁, Λ ((σ₁ s : ↥(t.X.lieOne (structureMap ι ψR))) : t.X.Lie) =
          ((σ₁' (I.τ₁ s) : ↥(t'.X.lieOne (structureMap ι ψR))) : t'.X.Lie)) ∧

        Submodule.map Λ.toLinearMap (t.X.lieZero (structureMap ι ψR)) = t'.X.lieZero (structureMap ι ψR) ∧
        Submodule.map Λ.toLinearMap (t.X.lieOne (structureMap ι ψR)) = t'.X.lieOne (structureMap ι ψR) ∧
        (∀ w : t.X.Lie, Λ (t.X.lieVarpi w) = t'.X.lieVarpi (Λ w)) ∧

        (∀ (w : t.X.Lie) (i : Fin 2), TrivSqZeroExt.fst (Λ w i) =
          (Matrix.mulVecLin (MvFormalGroup.linearPart u₀) (fun j => TrivSqZeroExt.fst (w j))) i) := by sorry
