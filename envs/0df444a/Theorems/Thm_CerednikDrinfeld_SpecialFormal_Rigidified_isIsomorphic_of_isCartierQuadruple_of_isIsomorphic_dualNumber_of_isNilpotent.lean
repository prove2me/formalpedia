-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isCartierQuadruple_of_isIsomorphic_dualNumber_of_isNilpotent
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isCartierQuadruple_of_isIsomorphic_dualNumber_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/3334186e-aa80-5dfb-868a-6412d6ab2e96
-- title:
--   First-order rigidity of rigidified special formal O_D-modules
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $O_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$, taken together with the reduction $\bar\jmath$ of $\iota$ modulo $p$. Assume: $\Phi$ is special for $\bar\jmath$, i.e. its Lie algebra is the direct sum of the complementary pieces $\mathrm{lieZero}$ and $\mathrm{lieOne}$, both invertible modules; $\Phi$ has height $4$, i.e. the action of $p$ has kernel of degree $p^4$; the operator $\mathrm{lieVarpi}$ induced by $\varpi$ annihilates $\mathrm{lieZero}$; the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary (hypothesis $hc_\Phi$), so that $\Phi$ yields graded Cartier module data $D_\Phi$; and an additive map $r_\Phi : \mathbb{Z}_p^2 \to D_\Phi.\mathrm{NMod}$ is given which, for every canonical $L$-map $L$ on $D_\Phi$, maps $\mathbb{Z}_p^2$ bijectively onto the $\eta$-piece of $D_\Phi$ in degree $0$. The conclusion asserts: for every algebraically closed field $\kappa$ that is a $\mathbb{Z}_p$-algebra, all ring homomorphisms $\psi_\kappa : W(k) \to \kappa$ and $\psi_R : W(k) \to \kappa[\varepsilon]$ into the dual numbers with $p$ nilpotent in $\kappa$ and in $\kappa[\varepsilon]$ and with $\psi_R$ followed by $\varepsilon \mapsto 0$ equal to $\psi_\kappa$, and all rigidified objects $t,t'$ over $\kappa[\varepsilon]$ (each a formal $O_D$-module $X$, an integer $n$ and a series $\rho$ over $\kappa[\varepsilon]/p$) that are admissible for $(\iota,\psi_R)$ — $X$ special, of height $4$, and $\rho$ an isogeny of height $4n$ from $\bar\Phi$ to $\bar X$ — whose base changes along $\varepsilon \mapsto 0$ are isomorphic as rigidified objects, and all Drinfeld data $Q,Q'$ over $\kappa[\varepsilon]$ for $\mathbb{Q}_p$ and the uniformiser $p$: if $t$ and $Q$, respectively $t'$ and $Q'$, are matched by `IsCartierQuadruple` relative to $\iota, hc_\Phi, r_\Phi, \psi_R$ (summarised: $\rho$ is an $O_D$-homomorphism; the invertible modules $T_0,T_1$ of the datum are identified with $\mathrm{lieZero}$ and $\mathrm{lieOne}$ of $X$ so that $\Pi_0,\Pi_1$ become $\mathrm{lieVarpi}$; and at each prime the lattices $N_0,N_1$ consist exactly of the vectors realised by $\eta$-sections of the graded Cartier module data of $t$ over basic opens, compatibly with the maps $u_0,u_1$), and $Q$ is isomorphic to $Q'$, then $t$ is isomorphic to $t'$, i.e. there are mutually inverse $O_D$-homomorphisms between their formal modules matching the rigidifications after multiplication by a power of $p$.
--
--   This is the first-order (dual-number) rigidity step in the Čerednik–Drinfeld uniformisation: a rigidified special formal $O_D$-module over $\kappa[\varepsilon]$ is determined up to isomorphism by its associated Drinfeld datum, given that the underlying reductions already agree. It is used to prove injectivity of the period map on dual-number points, from which the infinitesimal bijectivity of the Čerednik–Drinfeld comparison is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isCartierQuadruple_of_isIsomorphic_dualNumber_of_isNilpotent.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isCartierQuadruple_of_isIsomorphic_dualNumber_of_isNilpotent
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
    :
    ∀ (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra ℤ_[p] κ] (ψκ : WittVector p k →+* κ) (hκ : IsNilpotent (p : κ))
      (ψR : WittVector p k →+* DualNumber κ) (hR : IsNilpotent (p : DualNumber κ))
      (hresψ : ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ).comp ψR = ψκ)
      (t t' : Rigidified p Φ (DualNumber κ)),
      t.IsAdmissible ι ψR → t'.IsAdmissible ι ψR →
      (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).IsIsomorphic
        (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)) →
      ∀ (Q Q' : FormalOmega.DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) (DualNumber κ)),
        t.IsCartierQuadruple ι hcΦ rΦ ψR Q → t'.IsCartierQuadruple ι hcΦ rΦ ψR Q' →
        Q.IsIsomorphic Q' → t.IsIsomorphic t' := by sorry
