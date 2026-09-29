-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/504faebd-6fc4-5821-b52a-549c3ad9922a
-- title:
--   Translated rigidification numerator equals the A-twisted numerator
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and let $\Phi$ be a formal $\mathcal O_D$-module over $W(k)/p$ which is special and of height $4$ for the induced map $\bar\iota$ to $W(k)/p$, whose graded pieces in degrees $0$ and $1$ are complementary (hypothesis $h_{c\Phi}$), so that $\Phi$ gives graded Cartier module data with associated $N$-module; let $r_\Phi\colon\mathbb Z_p^2\to N(\Phi)$ be additive and such that for every canonical $L$-map $L$ it maps the whole of $\mathbb Z_p^2$ bijectively onto the degree-$0$ part of $\eta(L)$. Let $B$ be a Noetherian commutative $\mathbb Z_p$-algebra in which $p$ is nilpotent, $\psi\colon W(k)\to B$ a ring homomorphism, and let $E$ be an injective ring homomorphism from the centraliser of $\{\Phi.\mathrm{actEnd}\,a\}_a\cup\{\Phi.\mathrm{varpiEnd}\}$ in $\operatorname{End}(\Phi.F)$ into $M_2(\mathbb Q_p)$ such that $p^m E(e)$ is integral for every $e$ (for a fixed $m$), and such that whenever $p^mE(e)=A$ with $A$ over $\mathbb Z_p$ and $N_e$ is the endomorphism of $N(\Phi)$ induced by the action of $e$ on both Cartier-module components, $p^m\,N_e(r_\Phi w)=r_\Phi(Aw)$ for all $w\in\mathbb Z_p^2$. Let $e$ lie in that centraliser with kernel of degree $p^{2m'}$, let $g\in GL_2(\mathbb Q_p)$ equal $E(e)$, and $A$ over $\mathbb Z_p$ with $p^mE(e)=A$. Let $t=(X,n,\rho)$ be a rigidified object over $B$, admissible for $(\iota,\psi)$, and let $n'$, $\rho'$ be such that $(X,n',\rho')$ is admissible for $(\iota,\psi\circ\mathrm{Fr}^{m'})$ and is a translate of $t$ by $e$ in the sense of `IsTranslate` with $k=0$ and parameter $m'$. Then there exists $c\in\mathbb N$ with the following property: for all proofs that $\rho$ and $\rho'$ are $\mathcal O_D$-homomorphisms $\bar\Phi\to\bar X$ over $\psi$ and over $\psi\circ\mathrm{Fr}^{m'}$ respectively, every commutative ring $S$ and ring homomorphism $f\colon B\to S$, all three complementarity hypotheses for the graded pieces of $\bar X_S$ and of $\bar\Phi_S$ over $\psi$ and over $\psi\circ\mathrm{Fr}^{m'}$, every additive endomorphism $N_V$ of $N(\bar X_S)$ induced by the $m'$-fold integral Verschiebung on both components, and every $w\in\mathbb Z_p^2$, $$p^{\,c+n+m}\,N_V\bigl(N(\rho'_*)\,N(\mathrm{bc}_{\psi\circ\mathrm{Fr}^{m'}})\,(r_\Phi w)\bigr)=p^{\,c+n'}\,\mathrm{rigidNum}(w\mapsto N(\rho_*)\,N(\mathrm{bc}_\psi)\,r_\Phi)(Aw),$$ the left-hand composite being the rigidification numerator of the translated object and the right-hand side `t.rigidNum` evaluated at $Aw$.
--
--   This is the Cartier-module bookkeeping behind the $GL_2(\mathbb Q_p)$-equivariance of Drinfeld's classification of special formal $\mathcal O_D$-modules: it transports a translate relation between rigidified objects into an identity between their rigidification numerators, the isogeny $e$ acting on $\mathbb Z_p^2$ through the integral matrix $A=p^mE(e)$ and the height-$2m'$ shift being absorbed by $V^{m'}$. It is the common ingredient of the even and odd lattice-translate statements for Cartier quadruples and of the comparison of $\eta$-sections under translation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec.lean

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
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec
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
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hA : (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (n' : ℕ) (ρ' : Series (B ⧸ pIdeal p B))
    (ht' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')))
    (htr : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B)) :
    ∃ c : ℕ, ∀ (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
      (hOD' : FormalODModule.IsODHom (({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).Φbar (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m'))) t.Xbar ρ')
      {S : Type} [CommRing S] (f : B →+* S)
      (hcb : t.IsGradedSbar ι ψ f)
      (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ f) (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f)
      (NV : ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).NMod →+ ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).NMod)
      (hNV : ∀ x : MvFormalGroup.CartierModule p (t.XbarS f).F × MvFormalGroup.CartierModule p (t.XbarS f).F,
        NV (((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk x) = ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk ((MvFormalGroup.CartierModule.verschiebungInt)^[m'] x.1,
          (MvFormalGroup.CartierModule.verschiebungInt)^[m'] x.2))
      (w : Fin 2 → ℤ_[p]),
      p ^ (c + t.n + m) • NV (((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) hcΦf').nMap ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb)
            (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_verschiebungInt (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_endAct_varpiEnd (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' f)
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) hcΦf')
            (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) (rΦ w))) =
        p ^ (c + n') • t.rigidNum ι hcΦ rΦ ψ hOD f hcb hcΦf (A.mulVec w) := by sorry
