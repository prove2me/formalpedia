-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/7135636d-4197-537f-b40e-594ad80bb83d
-- title:
--   Tangent identity for u₁ over a field, index 1
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : \mathbb{Z}_{p^2} \to W(k)$ a ring homomorphism, where $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$. Let $\Phi$ be a formal $\mathcal{O}_D$-module over $W(k)/pW(k)$ whose graded pieces of weights $0$ and $1$ for the reduction $\bar\iota$ of $\iota$ are complementary ($h_{c\Phi}$), and let $r_\Phi : \mathbb{Z}_p^2 \to N(\Phi)$ be an additive map into the $N$-module of the graded Cartier module data attached to $\Phi$, $\bar\iota$ and $h_{c\Phi}$. Let $\kappa$ be a field of characteristic $p$ that is a $\mathbb{Z}_p$-algebra, $\psi : W(k) \to \kappa$ a ring homomorphism, and $t = (X, n, \rho)$ a rigidified datum over $\kappa$: a formal $\mathcal{O}_D$-module $X$, an integer $n$, and a $2$-tuple $\rho$ of power series over $\kappa/p\kappa$. Let $Q$ be a Drinfeld datum over $\kappa$ for $K = \mathbb{Q}_p$ and uniformiser $p \in \mathbb{Z}_p$, and let $\tau_0, \tau_1$ be $\kappa$-linear isomorphisms of $Q.T_0$, $Q.T_1$ onto the weight-$0$ and weight-$1$ subspaces of the Lie module of $X$ for the structure map $\psi \circ \iota$; assume `IsCartierQuadrupleVia` holds for these data, and that $\rho$ is a homomorphism of formal $\mathcal{O}_D$-modules from $\bar\Phi$ to $\bar X$ ($h_{OD}$). Base-change along the localisation $\kappa \to \kappa[1/1]$, written `awayHom 1`, and assume the three complementarity hypotheses $h_c$, $h_{cb}$, $h_{c\Phi g}$ for $X$, $\bar X$ and $\bar\Phi$ there. Let $L$ be an additive map from $M$ to its $N$-module which is a canonical $L$-map, $x$ a point of $\operatorname{Spec} \kappa$, $m \in M$, and $v \in \mathbb{Q}_p^2$, and assume the $\eta$-section condition in degree $1$ for the class of $(m,0)$ and $v$: that class lies in the degree-$1$ part of the $\eta$-subgroup determined by $L$, and the lattice relation between the rigidification map $r$ and the reduction of $\varpi$ applied once to the class holds for $p \cdot v$. Then there exist a proof that $v \in Q.N_1(x)$, an element $s \in Q.T_1$ and $b$ in the complement of the prime of $x$ such that $Q.u_1(x)(1 \otimes v) = s/b$ in the stalk of $T_1$ at $x$, the image of $b$ in $\kappa[1/1]$ is a unit, and for each $l \in \{0,1\}$ the image of the $l$-th coordinate of $\tau_1(s)$ equals that image of $b$ times the $l$-th tangent coordinate of $m$.
--
--   This is the $u_1$-clause of the Cartier-quadruple condition restated over a base field, with the stalk at $x$ eliminated: the identification of $\tau_1(s)$ with a multiple of the tangent vector of $m$ is recorded directly in the localisation $\kappa[1/1]$, and the auxiliary element $m_1$ furnished by the quadruple condition is replaced by $m$ itself. It feeds the construction of the injective linear map on the Lie quotient used in the Čerednik–Drinfeld comparison between rigidified special formal modules and Drinfeld data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one.lean

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
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t : Rigidified p Φ κ)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (τ₀ : Q.T₀ ≃ₗ[κ] ↥(t.X.lieZero (structureMap ι ψ)))
    (τ₁ : Q.T₁ ≃ₗ[κ] ↥(t.X.lieOne (structureMap ι ψ)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q τ₀ τ₁)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : κ)))
    (L : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) (hL : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).IsCanonicalLMap L)
    (x : PrimeSpectrum κ) (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (v : Fin 2 → ℚ_[p])
    (hsec : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL 1 (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0)) v) :
    ∃ (hv : v ∈ Q.N₁ x) (s : Q.T₁) (b : ↥(x.asIdeal.primeCompl)),
      Q.u₁ x ((1 : Rigidified.Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ x))) = LocalizedModule.mk s b ∧
      IsUnit (Rigidified.awayHom (1 : κ) (b : κ)) ∧
      ∀ l : Fin 2, Rigidified.awayHom (1 : κ) (((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) l) =
        Rigidified.awayHom (1 : κ) (b : κ) * MvFormalGroup.CartierModule.tangent m l := by sorry
