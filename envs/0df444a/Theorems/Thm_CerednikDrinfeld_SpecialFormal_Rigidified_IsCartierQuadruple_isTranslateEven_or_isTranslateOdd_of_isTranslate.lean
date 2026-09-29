-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isTranslateEven_or_isTranslateOdd_of_isTranslate
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isTranslateEven_or_isTranslateOdd_of_isTranslate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/f36e8459-f8e8-5aa2-a4b8-a3dcd988c980
-- title:
--   Cartier quadruples of e-translates are E(e)-translates
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota:\mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})\to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ over $W(k)/pW(k)$ (a two-dimensional commutative formal group law with an action of $\mathbb{Z}_{p^2}$ and an element $\varpi$ with $\varpi^2=[p]$, $\varpi\circ[a]=[\sigma a]\circ\varpi$). Assume, for the structure map $\bar\iota$ obtained from $\iota$ by reduction mod $p$: $\Phi$ is special (its Lie algebra splits into two invertible pieces), $\Phi$ has height $4$ (the kernel of $[p]$ has degree $p^4$), the eigenspaces $\Phi.\mathrm{gradedPiece}\,\bar\iota\,0$ and $\Phi.\mathrm{gradedPiece}\,\bar\iota\,1$ of the $\mathbb{Z}_{p^2}$-action on the Cartier module are complementary (hypothesis $h_{c\Phi}$, giving graded Cartier module data $D_\Phi$), and an additive map $r_\Phi:\mathbb{Z}_p^2\to D_\Phi.\mathrm{NMod}$ is given which, for every canonical $L$-map $L$, maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ part $D_\Phi.\mathrm{etaPiece}\,L\,\_\,0$. Let $B$ be a noetherian commutative $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi:W(k)\to B$ a ring homomorphism. Let $E$ be an injective ring homomorphism from the centralizer of $\{[a]\}_{a}\cup\{\varpi\}$ in $\mathrm{End}(\Phi.F)$ into $M_2(\mathbb{Q}_p)$, with $m\in\mathbb{N}$ such that $p^m E(e)$ is integral for every $e$, and compatible with $r_\Phi$ in the sense that whenever $p^mE(e)=A$ with $A\in M_2(\mathbb{Z}_p)$ and $N_e$ is the endomorphism of $D_\Phi.\mathrm{NMod}$ induced by the functorial action of $e$ on pairs (Cartier module, $\Sigma$-component), then $p^m\cdot N_e(r_\Phi w)=r_\Phi(Aw)$ for all $w\in\mathbb{Z}_p^2$. Let $e$ be an element of that centralizer whose kernel has degree $p^{2m'}$, and $g\in\mathrm{GL}_2(\mathbb{Q}_p)$ with underlying matrix $E(e)$. Let $t=(X,n,\rho)$ and $t'=(X',n',\rho')$ be rigidified data over $B$, with $t$ admissible for $(\iota,\psi)$ and $t'$ admissible for $(\iota,\psi\circ\mathrm{Fr}^{m'})$ (special, height $4$, with $\rho$ an isogeny of height $4n$ from $\bar\Phi$ to $\bar X$), and assume $t'$ is the $e$-translate of $t$ with parameters $k=0$, $m'$: $X'=X$ and for some $c$, $[p^{c+n}]\circ\rho'\circ\mathrm{Frob}^{m'}=[p^{c+n'}]\circ\rho\circ\bar e$. Finally let $Q,Q'$ be Drinfeld data over $B$ for $\pi=p\in\mathbb{Z}_p$, $K=\mathbb{Q}_p$, with $Q$ a Cartier quadruple of $t$ over $\psi$ and $Q'$ a Cartier quadruple of $t'$ over $\psi\circ\mathrm{Fr}^{m'}$ (the lattices $N_0,N_1$ being cut out by $\eta$-sections of the graded Cartier module of $X$ and the invertible modules $T_0,T_1$ identified with the two Lie pieces). Then either there is $c\in\mathbb{Q}_p^\times$ with $Q'$ an even translate of $Q$ by $(g,c)$, i.e. $N_i'(x)=(c\,g^{-1})N_i(x)$ for every prime $x$ of $B$ together with $B$-linear isomorphisms $\tau_0,\tau_1$ of the $T$-modules intertwining $\Pi_0,\Pi_1$ and the maps $u_0,u_1$; or there are $c_0,c_1\in\mathbb{Q}_p^\times$ with $c_0=p\,c_1$ and $Q'$ an odd translate of $Q$ by $(g,c_0,c_1)$, i.e. $N_0'(x)=(c_0g^{-1})N_1(x)$, $N_1'(x)=(c_1g^{-1})N_0(x)$ together with isomorphisms $\sigma_0:T_1\to T_0'$, $\sigma_1:T_0\to T_1'$ compatible with the $\Pi$'s and the $u$'s.
--
--   This is the translation-equivariance step in Drinfeld's classification of special formal $\mathcal{O}_D$-modules: passing from a rigidified datum to its translate under an $\mathcal{O}_D$-isogeny $e$ of height $2m'$ moves the associated Drinfeld datum by the matrix $E(e)\in\mathrm{GL}_2(\mathbb{Q}_p)$, up to a scalar and up to a shift of the grading when $m'$ is odd. It feeds the pull-back statement [`CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isPullback_of_isTranslate`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isPullback_of_isTranslate).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isTranslateEven_or_isTranslateOdd_of_isTranslate.lean

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

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isTranslateEven_or_isTranslateOdd_of_isTranslate
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
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) Q') :
    (∃ c : ℚ_[p]ˣ, Q.IsTranslateEven g c Q') ∨
      (∃ c₀ c₁ : ℚ_[p]ˣ, Q.IsTranslateOdd g c₀ c₁ Q') := by sorry
