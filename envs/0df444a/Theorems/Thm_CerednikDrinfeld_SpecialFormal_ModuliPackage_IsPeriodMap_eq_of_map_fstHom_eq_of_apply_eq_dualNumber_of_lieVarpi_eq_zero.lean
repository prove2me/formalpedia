-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_eq_of_map_fstHom_eq_of_apply_eq_dualNumber_of_lieVarpi_eq_zero
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.eq_of_map_fstHom_eq_of_apply_eq_dualNumber_of_lieVarpi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/81182844-38e9-5132-b772-e2cad87b403d
-- title:
--   Injectivity of the period map on dual-number points
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$ which, with respect to the structure map obtained from $\iota$ by reduction modulo $p$, is special (its Lie algebra is the direct sum of the two eigenpieces `lieZero` and `lieOne`, each invertible), has height $4$ in the sense that multiplication by $p$ has kernel of degree $p^4$, and satisfies $\mathrm{lieVarpi}(m)=0$ for every $m$ in `lieZero`. Let $M$ be a moduli package over $W(k)$ — a functor $B\mapsto M(B,\psi)$ on $W(k)$-algebras with $p$ nilpotent — which is a Zariski sheaf, and let $\eta$ assign to each rigidified object over $B$ a point of $M(B,\psi)$, subject to three conditions: over Noetherian $B$, two admissible rigidified objects have the same image under $\eta$ exactly when they are isomorphic; $\eta$ commutes with base change along maps of $W(k)$-algebras; and every point of $M(B,\psi)$ with $B$ Noetherian becomes, over each member of a finite Zariski cover of $\mathrm{Spec}\,B$ by localisations away from elements generating the unit ideal, the $\eta$-image of an admissible rigidified object. Assume further that the graded pieces of index $0$ and $1$ of the Cartier module of $\Phi$ are complements (`hcΦ`), let $r_\Phi\colon \mathbb Z_p^2\to \mathcal N$ be an additive map into the $N$-module of the associated graded Cartier module data, and assume that for every canonical $L$-map $L$ the map $r_\Phi$ is a bijection from the whole of $\mathbb Z_p^2$ onto the degree-$0$ $\eta$-piece of $L$. Finally let $\theta$ attach to each point of $M(B,\psi)$, for $B$ a Noetherian $\mathbb Z_p$-algebra with $p$ nilpotent, a Deligne datum over $B$ for the uniformiser $p$ of $\mathbb Z_p\subset\mathbb Q_p$, and assume `IsPeriodMap` for the tuple: any Drinfeld quadruple attached to an admissible rigidified $t$ is a quadruple of $\theta(\eta(t))$, and $\theta$ is compatible with base change. The conclusion: for every algebraically closed field $\kappa$ that is a Noetherian $\mathbb Z_p$-algebra, every $\psi_\kappa\colon W(k)\to\kappa$ with $p$ nilpotent in $\kappa$, every $\psi_R\colon W(k)\to\kappa[\varepsilon]$ with $p$ nilpotent in the dual numbers $\kappa[\varepsilon]$ and with $\psi_R$ followed by the projection $\varepsilon\mapsto 0$ equal to $\psi_\kappa$, every $x\in M(\kappa,\psi_\kappa)$ and every Deligne datum $d$ over $\kappa[\varepsilon]$ whose base change along $\varepsilon\mapsto 0$ is $\theta(x)$, any two points $y,y'\in M(\kappa[\varepsilon],\psi_R)$ that both restrict to $x$ along $\varepsilon\mapsto 0$ and both satisfy $\theta(y)=\theta(y')=d$ are equal.
--
--   This is the uniqueness half of the statement that the period morphism is bijective on dual-number points, i.e. injectivity of the period map on tangent spaces, as in Boutot–Carayol II (11.1). It feeds the general injectivity statement [`CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero) for the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_eq_of_map_fstHom_eq_of_apply_eq_dualNumber_of_lieVarpi_eq_zero.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.eq_of_map_fstHom_eq_of_apply_eq_dualNumber_of_lieVarpi_eq_zero
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)
(hθ : CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap p k ι Φ M η hcΦ rΦ θ)
    :
        (∀ (κ : Type) [Field κ] [IsAlgClosed κ] [IsNoetherianRing κ] [Algebra ℤ_[p] κ] (ψκ : WittVector p k →+* κ)
    (hκ : IsNilpotent (p : κ))
    (ψR : WittVector p k →+* DualNumber κ) (hR : IsNilpotent (p : DualNumber κ))
    (hresψ : ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ).comp ψR = ψκ)
    (x : M.obj κ ψκ hκ) (d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) (DualNumber κ)),
    DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p]))
      ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) d (θ κ ψκ hκ x) →
    ∀ y y' : M.obj (DualNumber κ) ψR hR,
      M.map hR hκ ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) hresψ y = x →
      θ (DualNumber κ) ψR hR y = d →
      M.map hR hκ ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) hresψ y' = x →
      θ (DualNumber κ) ψR hR y' = d → y = y') := by sorry
