-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_odd
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearEquiv_stalkMap_comp_of_isTranslate_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/2812059a-f364-5d9b-8713-5851d082cc46
-- title:
--   Cartier quadruples of an odd isogeny translate, pieces swapped
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbb{F}_{p^2})\to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ over $W(k)/pW(k)$ which is special for the reduction $\bar\iota$ of $\iota$ (its Lie pieces in degrees $0$ and $1$ are complementary and invertible) and of height $4$ (the kernel of multiplication by $p$ has degree $p^4$); let $hc_\Phi$ assert that the graded pieces of degrees $0$ and $1$ of the Cartier module of $\Phi$ for $\bar\iota$ are complementary, and let $r_\Phi\colon\mathbb{Z}_p^2\to N$ be an additive map into the $N$-module of the associated graded Cartier module data which maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece attached to every canonical $L$-map. Let $B$ be a Noetherian $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi\colon W(k)\to B$ a ring homomorphism, and $E$ an injective ring homomorphism from the centralizer of the $\mathcal{O}_D$-action together with $\varpi$ into $M_2(\mathbb{Q}_p)$ such that $p^m E(\cdot)$ is integral and such that, for $A$ integral with $p^mE(e)=A$ and $Ne$ the endomorphism of $N$ induced by $e$ on Cartier modules, $p^m\cdot Ne(r_\Phi w)=r_\Phi(Aw)$ for all $w\in\mathbb{Z}_p^2$. Let $e$ be an element of this centralizer whose kernel has degree $p^{2m'}$, and $g\in GL_2(\mathbb{Q}_p)$ with matrix $E(e)$. Let $t$ be a rigidified object over $B$, admissible for $(\iota,\psi)$, and $t'$ one admissible for $\psi\circ\mathrm{Frob}^{m'}$ which is the $e$-translate of $t$ with parameters $0,m'$ (so $t'.X=t.X$ and, for some $c$, $[p^{c+t.n}]\rho'\circ\mathrm{Frob}^{m'}=[p^{c+t'.n}]\rho\circ\bar e$). Let $Q,Q'$ be Drinfeld data over $B$ for $\pi=p$ with $K=\mathbb{Q}_p$ — full lattices $N_0\subseteq N_1$ in $\mathbb{Q}_p^2$ at each prime of $B$ with $pN_1\subseteq N_0$, invertible $B$-modules $T_0,T_1$ with maps $\Pi_0,\Pi_1$ composing to multiplication by $p$, and stalkwise comparison maps $u_0,u_1$ — and suppose $Q$ is a Cartier quadruple for $t$ over $\psi$ and $Q'$ one for $t'$ over $\psi\circ\mathrm{Frob}^{m'}$ (the defining conditions, which identify $T_0,T_1$ with the Lie pieces of $t.X$ compatibly with $\Pi$ and $\varpi$, describe membership in $N_0,N_1$ by local $\eta$-sections and compute $u_0,u_1$ from the canonical maps, being summarised here). Finally let $m'=2j+1$ and let $c_0=p^{j+1}$, $c_1=p^j$ in $\mathbb{Q}_p^\times$. Then there are $B$-linear isomorphisms $\sigma_0\colon Q.T_1\to Q'.T_0$ and $\sigma_1\colon Q.T_0\to Q'.T_1$ with $\sigma_1\circ\Pi_1=\Pi'_0\circ\sigma_0$ and $\sigma_0\circ\Pi_0=\Pi'_1\circ\sigma_1$, such that at every prime $x$ of $B$: for $w\in N_1(x)$ with $c_0g^{-1}w\in N'_0(x)$ one has $u'_{0,x}(1\otimes c_0g^{-1}w)$ equal to the localisation of $\sigma_0$ applied to $u_{1,x}(1\otimes w)$, and for $v\in N_0(x)$ with $c_1g^{-1}v\in N'_1(x)$ one has $u'_{1,x}(1\otimes c_1g^{-1}v)$ equal to the localisation of $\sigma_1$ applied to $u_{0,x}(1\otimes v)$.
--
--   This is the odd case of the comparison, in the Čerednik–Drinfeld uniformisation, between the Drinfeld datum attached to a rigidified special formal $\mathcal{O}_D$-module and the one attached to its translate by an $\mathcal{O}_D$-linear isogeny $e$ of height $2m'$: for $m'$ odd the two degrees are interchanged, the lattice comparison involving the homotheties $p^{j+1}$ and $p^{j}$ together with $g^{-1}=E(e)^{-1}$. It is used, alongside its even counterpart, in the case distinction `isTranslateEven_or_isTranslateOdd_of_isTranslate`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_odd.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearEquiv_stalkMap_comp_of_isTranslate_of_odd
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
    (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) Q')
    (j : ℕ) (hm' : m' = 2 * j + 1) (c₀ c₁ : ℚ_[p]ˣ)
    (hc₀ : (c₀ : ℚ_[p]) = (p : ℚ_[p]) ^ (j + 1)) (hc₁ : (c₁ : ℚ_[p]) = (p : ℚ_[p]) ^ j) :
    ∃ (σ₀ : Q.T₁ ≃ₗ[B] Q'.T₀) (σ₁ : Q.T₀ ≃ₗ[B] Q'.T₁),
      (∀ s, σ₁ (Q.Pi₁ s) = Q'.Pi₀ (σ₀ s)) ∧ (∀ s, σ₀ (Q.Pi₀ s) = Q'.Pi₁ (σ₁ s)) ∧
      (∀ (x : PrimeSpectrum B) (w : Fin 2 → ℚ_[p]) (hw : w ∈ Q.N₁ x)
        (hw' : ((scalarGL c₀ * g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).mulVec w ∈ Q'.N₀ x),
        Q'.u₀ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨_, hw'⟩ : ↥(Q'.N₀ x))) =
          LocalizedModule.map x.asIdeal.primeCompl σ₀.toLinearMap
            (Q.u₁ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨w, hw⟩ : ↥(Q.N₁ x))))) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ x)
        (hv' : ((scalarGL c₁ * g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).mulVec v ∈ Q'.N₁ x),
        Q'.u₁ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨_, hv'⟩ : ↥(Q'.N₁ x))) =
          LocalizedModule.map x.asIdeal.primeCompl σ₁.toLinearMap
            (Q.u₀ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ x))))) := by sorry
