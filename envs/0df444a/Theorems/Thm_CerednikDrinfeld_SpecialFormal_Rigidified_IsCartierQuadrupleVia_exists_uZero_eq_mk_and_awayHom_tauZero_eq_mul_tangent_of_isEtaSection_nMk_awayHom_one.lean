-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_uZero_eq_mk_and_awayHom_tauZero_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_uZero_eq_mk_and_awayHom_tauZero_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/070d3d89-a347-5c5a-8fa6-539dcd681f0a
-- title:
--   Tangent form of the u₀ clause over a field
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $O_D$-module $\Phi$ over $W(k)/pW(k)$ whose graded pieces of weights $0$ and $1$ for the induced map $\bar\iota$ are complementary (hypothesis $h_{c\Phi}$), together with an additive map $r_\Phi$ from $\mathbb{Z}_p^2$ to the $N$-module of the graded Cartier module data of $\Phi$. Let $\kappa$ be a field of characteristic $p$ that is a $\mathbb{Z}_p$-algebra, $\psi : W(k) \to \kappa$ a ring homomorphism, $t$ a rigidified object (a formal $O_D$-module $t.X$ over $\kappa$, an integer $t.n$ and a series $t.\rho$ over $\kappa/p\kappa$), $Q$ a Drinfeld datum over $\kappa$ for the uniformiser $p \in \mathbb{Z}_p$, and $\tau_0, \tau_1$ $\kappa$-linear isomorphisms from $Q.T_0$, $Q.T_1$ onto the weight-$0$ and weight-$1$ parts of the Lie module $t.X.\mathrm{Lie}$ for the structure map $\psi \circ \iota$. Assume $(t,Q,\tau_0,\tau_1)$ satisfies `IsCartierQuadrupleVia`, that $t.\rho$ is an $O_D$-module homomorphism from $\Phi$ reduced along $\psi$ to $\bar{t.X}$, and fix the complementarity hypotheses `hc`, `hcb`, `hcΦg` for the localisation $\kappa_{(1)}$ of $\kappa$ away from $1$, an additive map $L$ from $M$ to the $N$-module of the corresponding graded Cartier module data with `hL` asserting that $L$ is a canonical $L$-map. Finally let $x$ be a point of $\operatorname{Spec}\kappa$, $m \in M$, $v \in \mathbb{Q}_p^2$, and assume `IsEtaSection` holds at index $0$ for the class $\mathrm{nMk}(m,0)$ and $v$. Then $v$ lies in $Q.N_0(x)$ and there are $s \in Q.T_0$ and $b \in \kappa$ outside the prime ideal of $x$ with $Q.u_0(x)(1 \otimes v) = s/b$ in the stalk of $T_0$ at $x$, with the image of $b$ in $\kappa_{(1)}$ a unit, and with the image of $\tau_0(s)_l$ in $\kappa_{(1)}$ equal to the image of $b$ times $\mathrm{tangent}(m)_l$ for $l = 0, 1$.
--
--   This is the $u_0$-clause of the Cartier-quadruple condition specialised to a base field $\kappa$ and to the localisation away from $1$: the comparison identity between the Drinfeld lattice data and the tangent vector of the Cartier module element is read off directly, with the given $m$ rather than an auxiliary representative, and with $b$ visibly invertible. It feeds the construction of the injective map on the Lie quotient in [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_uZero_eq_mk_and_awayHom_tauZero_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_uZero_eq_mk_and_awayHom_tauZero_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
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
    (hsec : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL 0 (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0)) v) :
    ∃ (hv : v ∈ Q.N₀ x) (s : Q.T₀) (b : ↥(x.asIdeal.primeCompl)),
      Q.u₀ x ((1 : Rigidified.Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ x))) = LocalizedModule.mk s b ∧
      IsUnit (Rigidified.awayHom (1 : κ) (b : κ)) ∧
      ∀ l : Fin 2, Rigidified.awayHom (1 : κ) (((τ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) l) =
        Rigidified.awayHom (1 : κ) (b : κ) * MvFormalGroup.CartierModule.tangent m l := by sorry
