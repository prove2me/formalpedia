-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_apply_tau_eq_of_iso
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_linearEquiv_lie_apply_tau_eq_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/ee97983f-a553-5915-b0f5-108ae47467cd
-- title:
--   Isomorphic Drinfeld data induce compatible Lie-module isomorphisms
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbb{F}_{p^2})\to W(k)$ (where $W(\mathbb{F}_{p^2})$ is written `Zp2 p`), and a formal $\mathcal{O}_D$-module $\Phi$ over $W(k)/pW(k)$; fix further a field $\kappa$ of characteristic $p$ that is a $\mathbb{Z}_p$-algebra and a ring homomorphism $\psi\colon W(k)\to\kappa$, and write $j=\psi\circ\iota$ for the induced map `structureMap ι ψ`. Let $t,t'$ be rigidified objects over $\kappa$ relative to $\Phi$, each carrying a formal $\mathcal{O}_D$-module $t.X$ with tangent module $t.X.\mathrm{Lie}=\kappa^{2}$; assume that inside $t.X.\mathrm{Lie}$ the submodule $\mathrm{lieZero}$, the intersection over $a\in W(\mathbb{F}_{p^2})$ of the kernels of $\mathrm{lieAct}(a)-j(a)\cdot\mathrm{id}$, and the submodule $\mathrm{lieOne}$, defined in the same way with $j(\mathrm{Frob}\,a)$ in place of $j(a)$, are complementary, and likewise for $t'$. Let $Q,Q'$ be Drinfeld data over $\kappa$ for $\mathcal{O}=\mathbb{Z}_p$, $K=\mathbb{Q}_p$ and uniformiser $\pi=p$, with invertible $\kappa$-modules $Q.T_0,Q.T_1$ and $Q'.T_0,Q'.T_1$, let $\tau_0,\tau_1$ be $\kappa$-linear isomorphisms of $Q.T_0,Q.T_1$ onto the two complementary submodules of $t.X.\mathrm{Lie}$, let $\tau_0',\tau_1'$ be the analogous isomorphisms for $Q'$ and $t'$, and let $e$ be an isomorphism of Drinfeld data from $Q$ to $Q'$, with underlying linear isomorphisms $e.\tau_0\colon Q.T_0\to Q'.T_0$ and $e.\tau_1\colon Q.T_1\to Q'.T_1$. Then there exists a $\kappa$-linear isomorphism $\sigma\colon t.X.\mathrm{Lie}\to t'.X.\mathrm{Lie}$ such that $\sigma(\tau_0 s)=\tau_0'(e.\tau_0 s)$ for all $s\in Q.T_0$ and $\sigma(\tau_1 s)=\tau_1'(e.\tau_1 s)$ for all $s\in Q.T_1$, the values being taken in the ambient tangent modules. Despite its placement in the `IsCartierQuadrupleVia` namespace, the statement assumes no compatibility of $t,t'$ with $Q,Q'$ beyond the existence of the four linear identifications.
--
--   This is the tangent-level half of the comparison between a rigidified special formal $\mathcal{O}_D$-module and its associated Drinfeld datum in the Čerednik–Drinfeld uniformisation: an isomorphism of Drinfeld data is transported to an isomorphism of two-dimensional tangent modules respecting the two eigencomponents for the action of $W(\mathbb{F}_{p^2})$. It feeds the assembly of the statement that Cartier quadruples with isomorphic Drinfeld data have isomorphic tangent quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_apply_tau_eq_of_iso.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_linearEquiv_lie_apply_tau_eq_of_iso
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t t' : Rigidified p Φ κ)
    (hLie : IsCompl (t.X.lieZero (structureMap ι ψ)) (t.X.lieOne (structureMap ι ψ)))
    (hLie' : IsCompl (t'.X.lieZero (structureMap ι ψ)) (t'.X.lieOne (structureMap ι ψ)))
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (τ₀ : Q.T₀ ≃ₗ[κ] ↥(t.X.lieZero (structureMap ι ψ)))
    (τ₁ : Q.T₁ ≃ₗ[κ] ↥(t.X.lieOne (structureMap ι ψ)))
    (τ₀' : Q'.T₀ ≃ₗ[κ] ↥(t'.X.lieZero (structureMap ι ψ)))
    (τ₁' : Q'.T₁ ≃ₗ[κ] ↥(t'.X.lieOne (structureMap ι ψ)))
    (e : DrinfeldDatum.Iso Q Q') :
    ∃ σ : t.X.Lie ≃ₗ[κ] t'.X.Lie,
      (∀ s : Q.T₀, σ ((τ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) =
        ((τ₀' (e.τ₀ s) : ↥(t'.X.lieZero (structureMap ι ψ))) : t'.X.Lie)) ∧
      (∀ s : Q.T₁, σ ((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) =
        ((τ₁' (e.τ₁ s) : ↥(t'.X.lieOne (structureMap ι ψ))) : t'.X.Lie)) := by sorry
