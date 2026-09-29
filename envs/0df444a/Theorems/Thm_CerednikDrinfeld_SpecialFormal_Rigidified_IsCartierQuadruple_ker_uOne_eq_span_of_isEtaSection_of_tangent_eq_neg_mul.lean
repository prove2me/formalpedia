-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_ker_uOne_eq_span_of_isEtaSection_of_tangent_eq_neg_mul
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.ker_uOne_eq_span_of_isEtaSection_of_tangent_eq_neg_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/5716dfaf-771e-5056-8546-11f74c5f8b06
-- title:
--   Kernel of u₁ at a point is the line c⊗ e₀+1⊗ e₁
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota\colon \mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})\to W(k)$. Let $\Phi$ be a formal $\mathcal{O}_D$-module over $W(k)/pW(k)$ whose Cartier module, graded by the reduction $\bar\iota$ of $\iota$, has complementary pieces of degrees $0$ and $1$ (hypothesis $h_{c\Phi}$), and let $r_\Phi\colon \mathbb{Z}_p^2\to N(\Phi)$ be an additive map into the associated $N$-module. Let $\kappa$ be a field of characteristic $p$ which is a $\mathbb{Z}_p$-algebra, $\psi\colon W(k)\to\kappa$ a ring homomorphism, $t=(X,n,\rho)$ a rigidified object over $\kappa$, and $Q$ a Drinfeld datum over $\kappa$ for $p\in\mathbb{Z}_p\subset\mathbb{Q}_p$, subject to $t.\mathrm{IsCartierQuadruple}\ \iota\ h_{c\Phi}\ r_\Phi\ \psi\ Q$; assume moreover that $\rho$ is an $\mathcal{O}_D$-homomorphism from the reduction of $\Phi$ along $\psi$ to $\bar X$. Fix $x\in\operatorname{Spec}\kappa$ and $f\in\kappa$ with $f\notin x$, and assume that over the localisation away from $f$ the degree-$0$ and degree-$1$ graded pieces are complementary for $X_f$, for $\bar X_f$ and for the reduction of $\Phi$ (hypotheses $h_c$, $h_{cb}$, $h_{c\Phi g}$). Let $L$ be a canonical $L$-map on the graded Cartier module data $D$ of $X_f$, let $e$ be a $\mathbb{Z}_p$-basis of $N_1(x)\subseteq\mathbb{Q}_p^2$ indexed by $\{0,1\}$, and let $z_0,z_1\in N(D)$ be $\eta$-sections in degree $1$ over the vectors $e_0$ and $e_1$ respectively, in the sense that each $z_i$ lies in the degree-$1$ part of $\eta(L)$ and its reduction, after applying $\varpi$ once, satisfies the lattice relation with the rigidification $r_\Phi$ transported to $\bar X_f$ against $p\cdot e_i$. Let $m_0,m_1\in D.M$ be elements whose classes in $D.M/V\,D.M$ are $u(L)(z_0)$ and $u(L)(z_1)$. Suppose there is $c\in\kappa$ with $\mathrm{tangent}(m_1)_j=-\,f\text{-localised}(c)\cdot \mathrm{tangent}(m_0)_j$ for both $j$, and that $\mathrm{tangent}(m_0)\neq 0$. Then the kernel of the stalk map $Q.u_1(x)$ is the $\kappa_x$-submodule of $\kappa_x\otimes_{\mathbb{Z}_p}N_1(x)$ spanned by the single element $c\otimes e_0+1\otimes e_1$.
--
--   This is the linear-algebra core of the recognition of Drinfeld's period point: it converts a proportionality relation between the tangent vectors of the two $\eta$-sections presenting a basis of the degree-$1$ lattice into the exact kernel of the degree-$1$ stalk map of the quadruple. It is used in the node case, the $\xi$-branch case and the $\eta$-branch case of the computation of this kernel for the explicit edge family of special formal $\mathcal{O}_D$-modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_ker_uOne_eq_span_of_isEtaSection_of_tangent_eq_neg_mul.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped TensorProduct PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.ker_uOne_eq_span_of_isEtaSection_of_tangent_eq_neg_mul
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t : Rigidified p Φ κ) (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (x : PrimeSpectrum κ) (f : κ) (hf : f ∉ x.asIdeal)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
    (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod)
    (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
    (e : Module.Basis (Fin 2) ℤ_[p] ↥(Q.N₁ x))
    (z₀ z₁ : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod)
    (hz₀ : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom f) hc hcb hcΦg L hL 1 z₀ ((e 0 : ↥(Q.N₁ x)) : Fin 2 → ℚ_[p]))
    (hz₁ : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom f) hc hcb hcΦg L hL 1 z₁ ((e 1 : ↥(Q.N₁ x)) : Fin 2 → ℚ_[p]))
    (m₀ m₁ : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M)
    (hm₀ : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).vRange.mkQ m₀ = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀.1).1⟩)
    (hm₁ : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).vRange.mkQ m₁ = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁.1).1⟩)
    (c : κ)
    (htan : ∀ j : Fin 2, MvFormalGroup.CartierModule.tangent m₁ j =
      -(Rigidified.awayHom f c) * MvFormalGroup.CartierModule.tangent m₀ j)
    (hne : ∃ j : Fin 2, MvFormalGroup.CartierModule.tangent m₀ j ≠ 0) :
    LinearMap.ker (Q.u₁ x) = Submodule.span (locRing κ x)
      {algebraMap κ (locRing κ x) c ⊗ₜ[ℤ_[p]] (e 0) + (1 : locRing κ x) ⊗ₜ[ℤ_[p]] (e 1)} := by sorry
