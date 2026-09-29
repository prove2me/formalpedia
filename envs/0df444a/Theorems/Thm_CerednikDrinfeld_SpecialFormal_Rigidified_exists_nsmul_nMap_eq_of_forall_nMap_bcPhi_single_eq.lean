-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/c2c81802-e2be-5120-b400-d5a44c15e447
-- title:
--   Rigidity up to a power of p for maps on N-modules
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbf F_{p^2})\to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ over $W(k)/p$ (a two-dimensional commutative formal group with an action of $W(\mathbf F_{p^2})$ and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$) which is special for the reduction of $\iota$, has height $4$ (the kernel of $[p]$ has degree $p^4$), and whose Cartier module has complementary graded pieces of weights $0$ and $1$, giving graded Cartier module data $D_\Phi$. Let $r_\Phi\colon(\mathbb Z_p)^2\to N(D_\Phi)$ be additive and assume it maps the whole source bijectively onto the degree-$0$ piece of $\eta(L)$ for every canonical $L\colon D_\Phi.M\to N(D_\Phi)$. Let $\psi\colon W(k)\to B$, let $t'$ be a rigidified datum over $B$ admissible for $(\iota,\psi)$, let $g\colon B\to S$, and suppose the Cartier modules of $\bar\Phi_S$ and of $\bar X'_S$ carry the corresponding complementarity, giving data $D_{\bar\Phi_S}$, $D_{\bar X'_S}$. Let $f_1,f_2\colon D_{\bar\Phi_S}.M\to D_{\bar X'_S}.M$ be additive, $W(S/p)$-linear, and compatible with $V$ and with $\varpi$, and let $e_1,e_2\in\mathbb N$. If $e_1\cdot N(f_1)(N(\mathrm{bc}_\Phi)(r_\Phi(\delta_i)))=e_2\cdot N(f_2)(N(\mathrm{bc}_\Phi)(r_\Phi(\delta_i)))$ for both standard basis vectors $\delta_i$ of $(\mathbb Z_p)^2$, where $\mathrm{bc}_\Phi$ is the base-change map of Cartier modules and $N(\cdot)$ the induced map of $N$-modules, then there is $a\in\mathbb N$ with $p^a\cdot e_1\cdot N(f_1)(z)=p^a\cdot e_2\cdot N(f_2)(z)$ for all $z\in N(D_{\bar\Phi_S})$.
--
--   This is the rigidity step for maps out of the constant family in the Čerednik–Drinfeld uniformisation: agreement of two $V$- and $\varpi$-compatible $W(S/p)$-linear maps on the image of the rigidification of the $(\mathbb Z_p)^2$-lattice forces agreement on the whole $N$-module after multiplication by a suitable power of $p$. It is used in the construction of the bijection attached to a Cartier quadruple.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] (ψ : WittVector p k →+* B)
    (t' : Rigidified p Φ B) (ht' : t'.IsAdmissible ι ψ)
    {S : Type} [CommRing S] (g : B →+* S)
    (hcb' : t'.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (f₁ f₂ : MvFormalGroup.CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g).F →+
      MvFormalGroup.CartierModule p (t'.XbarS g).F)
    (hW₁ : ∀ (w : WittVector p (S ⧸ pIdeal p S)) (x : MvFormalGroup.CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g).F),
      f₁ (w • x) = w • f₁ x)
    (hW₂ : ∀ (w : WittVector p (S ⧸ pIdeal p S)) (x : MvFormalGroup.CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g).F),
      f₂ (w • x) = w • f₂ x)
    (hV₁ : ∀ x, f₁ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).verschiebung x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').verschiebung (f₁ x))
    (hPi₁ : ∀ x, f₁ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).varpi x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').varpi (f₁ x))
    (hV₂ : ∀ x, f₂ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).verschiebung x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').verschiebung (f₂ x))
    (hPi₂ : ∀ x, f₂ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).varpi x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').varpi (f₂ x))
    (e₁ e₂ : ℕ)
    (hgen : ∀ i : Fin 2,
      e₁ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₁ hV₁ hPi₁
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
            (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g) (rΦ (Pi.single i 1))) =
        e₂ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₂ hV₂ hPi₂
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
            (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g) (rΦ (Pi.single i 1)))) :
    ∃ a : ℕ, ∀ z : ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).NMod,
      p ^ a • (e₁ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₁ hV₁ hPi₁ z) =
        p ^ a • (e₂ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₂ hV₂ hPi₂ z) := by sorry
