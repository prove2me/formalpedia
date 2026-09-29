-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_isPullback_of_isTranslate
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isPullback_of_isTranslate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/7dde4162-e6e6-51fb-9530-5c9a774077d7
-- title:
--   Isogeny translation pulls period values back along E(e)
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring map $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ over $W(k)/pW(k)$ (a two-dimensional commutative formal group law with a $W(\mathbb F_{p^2})$-action and a $\varpi$ satisfying $\varpi\circ\varpi=[p]$, $\varpi\circ[a]=[\sigma a]\circ\varpi$). Assume: $\Phi$ is special for the reduction $\bar\jmath$ of $\iota$ (its Lie pieces in degrees $0,1$ are complementary and invertible); $\Phi$ has height $4$, i.e. the kernel of $[p]$ is finite projective of rank $p^4$ at all field-valued points; `hc`$\Phi$ asserts that the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary; $r_\Phi\colon\mathbb Z_p^2\to N$ is an additive map into the $N$-module of the associated graded Cartier module data which, for every canonical $L$-map $L$, maps $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$. Further, $B$ is a Noetherian commutative $\mathbb Z_p$-algebra with $p$ nilpotent, $\psi\colon W(k)\to B$ a ring map, and $E$ an injective ring map from the centralizer of $\{\Phi.\mathrm{actEnd}(a)\}_a\cup\{\Phi.\mathrm{varpiEnd}\}$ in $\operatorname{End}(\Phi.F)$ to $M_2(\mathbb Q_p)$ such that, for some fixed $m$, every $p^mE(e)$ is integral, and such that whenever $p^mE(e)=A$ with $A\in M_2(\mathbb Z_p)$ and $N_e$ is the endomorphism of $N$ induced by the Cartier action of $e$ on both coordinates through `nMk`, one has $p^mN_e(r_\Phi w)=r_\Phi(Aw)$ for all $w\in\mathbb Z_p^2$. Given $e$ in that centralizer and $m'$ with the kernel of $e$ of degree $p^{2m'}$, $g\in GL_2(\mathbb Q_p)$ with $g=E(e)$, rigidified data $t,t'$ over $B$ with $t$ admissible for $(\iota,\psi)$ and $t'$ admissible for $(\iota,\psi\circ\mathrm{Fr}^{m'})$, $t'$ the $e$-translate of $t$ in degree $0$ with shift $m'$, and Deligne data $d,d'$ over $B$ for $\mathcal O=\mathbb Z_p\subset K=\mathbb Q_p$, $\pi=p$ such that $d$ is a period value of $t$ and $d'$ a period value of $t'$ (each via a Drinfeld datum forming a Cartier quadruple for the respective rigidified datum and a quadruple of the respective Deligne datum), the conclusion is that $d'$ is the pull-back of $d$ along $g$: for every full $\mathbb Z_p$-lattice $M\subset\mathbb Q_p^2$, the line $d'(M)$ equals the preimage of $d(gM)$ under the base change to $B$ of the isomorphism $M\to gM$.
--
--   This is the $GL_2(\mathbb Q_p)$-equivariance of the period map of the Čerednik–Drinfeld uniformisation: translating a rigidified special formal $\mathcal O_D$-module by an $\mathcal O_D$-isogeny $e$ of height $2m'$ transforms the associated point of Deligne's functor by the matrix $E(e)$. It is used in the construction of the local period morphism and in the statement comparing Drinfeld data with Deligne data up to isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_isPullback_of_isTranslate.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isPullback_of_isTranslate
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p]) (m : ℕ)
    (hEinj : Function.Injective E)
    (hEord : ∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hEcompat : (∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) →
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p ^ m • Ne (rΦ w) = rΦ (A.mulVec w)))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m')))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = E e)
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (ht' : t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')))
    (htr : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t t')
    (d d' : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hd : t.IsPeriodValue ι hcΦ rΦ ψ d)
    (hd' : t'.IsPeriodValue ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) d') :
    DeligneDatum.IsPullback (K := ℚ_[p]) (π := (p : ℤ_[p])) B g d d' := by sorry
