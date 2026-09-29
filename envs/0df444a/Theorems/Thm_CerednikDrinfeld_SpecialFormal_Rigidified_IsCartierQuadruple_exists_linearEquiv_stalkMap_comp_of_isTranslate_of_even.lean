-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_even
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearEquiv_stalkMap_comp_of_isTranslate_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/becbea55-6257-5c04-a818-f4d8f0efcb9b
-- title:
--   Cartier quadruples match under an even isogeny translate
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota\colon W(\mathbb F_{p^2})\to W(k)$ a ring homomorphism, with $\bar\iota$ its reduction modulo $p$. Let $\Phi$ be a formal $\mathcal O_D$-module over $W(k)/p$, i.e. a commutative two-dimensional formal group law $F$ together with an action of $W(\mathbb F_{p^2})$ by endomorphisms and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$; assume $\Phi$ is special (its Lie algebra is the direct sum of two complementary invertible pieces for $\bar\iota$) and of height $4$ (the kernel of $[p]$ is finite projective of degree $p^4$). Assume further that the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ — those elements on which the Teichmüller endomorphism $[\omega]$ acts as homothety by $\bar\iota(\omega)^{p^n}$, $n=0,1$ — are complementary, let $D_\Phi$ be the associated graded Cartier module data, and let $r_\Phi\colon\mathbb Z_p^2\to N(D_\Phi)$ be an additive map carrying $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece of every canonical $L$-map $L$ of $D_\Phi$. Let $B$ be a Noetherian $\mathbb Z_p$-algebra in which $p$ is nilpotent, $\psi\colon W(k)\to B$ a ring homomorphism, and $E$ an injective ring homomorphism from the centraliser of the $\mathcal O_D$-action (the endomorphisms of $F$ commuting with all $[a]$ and with $\varpi$) into $M_2(\mathbb Q_p)$ such that $p^mE(e)$ has entries in $\mathbb Z_p$ for all $e$, and such that whenever $p^mE(e)=A$ with $A$ over $\mathbb Z_p$ and $N_e$ is an additive endomorphism of $N(D_\Phi)$ induced by the action of $e$ on Cartier-module pairs (via $\mathrm{nMk}$, with the Frobenius twist on the second component), one has $p^m\,N_e(r_\Phi(w))=r_\Phi(Aw)$ for all $w\in\mathbb Z_p^2$. Let $e$ be such an endomorphism whose kernel has degree $p^{2m'}$, and $g\in GL_2(\mathbb Q_p)$ with $g=E(e)$. Let $t,t'$ be rigidified data over $B$ (a formal $\mathcal O_D$-module $X$, an integer $n$, a series $\rho$ over $B/p$), admissible for $\iota,\psi$ respectively for $\iota,\psi\circ\mathrm{Frob}^{m'}$ (special Lie algebra, height $4$, $\rho$ an isogeny of height $4n$ from the reduction of $\Phi$ to $\bar X$), and assume $t'$ is the $e$-translate of $t$ with parameters $0,m'$: $t'.X=t.X$ and $[p^{c+t.n}]\circ(t'.\rho\circ\mathrm{Frob}_{m'})=[p^{c+t'.n}]\circ(t.\rho\circ\bar e)$ for some $c$. Let $Q,Q'$ be Drinfeld data over $B$ for the uniformiser $p$ of $\mathbb Z_p\subset\mathbb Q_p$ (stalkwise full lattices $N_0(x)\subseteq N_1(x)\subseteq\mathbb Q_p^2$ with $pN_1(x)\subseteq N_0(x)$ and open membership conditions, invertible $B$-modules $T_0,T_1$ with maps $\Pi_0,\Pi_1$ whose composites are multiplication by $p$, and stalkwise trivialisations $u_0,u_1$), and assume $Q$ is a Cartier quadruple for $(t,\psi)$ and $Q'$ one for $(t',\psi\circ\mathrm{Frob}^{m'})$ with respect to $\iota$, the complementation hypothesis and $r_\Phi$; this pins $T_0,T_1$ to the two Lie pieces of $t.X$ compatibly with $\Pi_0,\Pi_1$ and $\varpi$, and describes $N_i(x)$ and $u_i$ by sections of the degree-$i$ $\eta$-pieces over Zariski neighbourhoods of $x$. Finally let $m'=2j$ and let $c\in\mathbb Q_p^\times$ with $c=p^j$. Then there exist $B$-linear isomorphisms $\tau_0\colon Q.T_0\xrightarrow{\sim}Q'.T_0$ and $\tau_1\colon Q.T_1\xrightarrow{\sim}Q'.T_1$ with $\tau_1(\Pi_0 s)=\Pi'_0(\tau_0 s)$ and $\tau_0(\Pi_1 s)=\Pi'_1(\tau_1 s)$, such that for $i=0,1$, every prime $x$ of $B$ and every $v\in N_i(x)$ with $cg^{-1}v\in N'_i(x)$, one has $u'_{i,x}(1\otimes cg^{-1}v)$ equal to the image of $u_{i,x}(1\otimes v)$ under the localisation of $\tau_i$ at the prime complement of $x$.
--
--   This is the tangent-and-stalk half of the $GL_2(\mathbb Q_p)$-equivariance in the Čerednik–Drinfeld uniformisation: for an isogeny translate with even parameter $m'=2j$ the two rigidifications share the same underlying formal $\mathcal O_D$-module, so the Drinfeld data attached to $t$ and $t'$ are identified by scaling the lattices by $p^jg^{-1}$. It feeds the case distinction on the parity of $m'$ in [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isTranslateEven_or_isTranslateOdd_of_isTranslate`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isTranslateEven_or_isTranslateOdd_of_isTranslate).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_even.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearEquiv_stalkMap_comp_of_isTranslate_of_even
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
    (j : ℕ) (hm' : m' = 2 * j) (c : ℚ_[p]ˣ) (hc : (c : ℚ_[p]) = (p : ℚ_[p]) ^ j) :
    ∃ (τ₀ : Q.T₀ ≃ₗ[B] Q'.T₀) (τ₁ : Q.T₁ ≃ₗ[B] Q'.T₁),
      (∀ s, τ₁ (Q.Pi₀ s) = Q'.Pi₀ (τ₀ s)) ∧ (∀ s, τ₀ (Q.Pi₁ s) = Q'.Pi₁ (τ₁ s)) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ x)
        (hv' : ((scalarGL c * g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).mulVec v ∈ Q'.N₀ x),
        Q'.u₀ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨_, hv'⟩ : ↥(Q'.N₀ x))) =
          LocalizedModule.map x.asIdeal.primeCompl τ₀.toLinearMap
            (Q.u₀ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ x))))) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₁ x)
        (hv' : ((scalarGL c * g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).mulVec v ∈ Q'.N₁ x),
        Q'.u₁ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨_, hv'⟩ : ↥(Q'.N₁ x))) =
          LocalizedModule.map x.asIdeal.primeCompl τ₁.toLinearMap
            (Q.u₁ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ x))))) := by sorry
