-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_u_baseChange
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/fbd89885-73d1-54a4-909f-881ff5c8b286
-- title:
--   Base change of the stalk maps u₀,u₁ of a Cartier quadruple
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring with a ring homomorphism $\iota:\mathbb{W}(\mathbb{F}_{p^2})\to O$, and $\Phi$ a formal $O_D$-module of relative dimension $2$ over $O/pO$, assumed special for $\bar\jmath=\iota$ followed by reduction (its Lie algebra splits into complementary invertible $\iota$- and Frobenius-$\iota$-eigenmodules) and of height $4$; let $hc\Phi$ split the Cartier module of $\Phi$ into the two graded pieces of degrees $0$ and $1$, and let $r_\Phi:\mathbb{Z}_p^2\to N(\Phi)$ be an additive map which, for every canonical $L$-map $L$ on the associated graded Cartier module datum, carries all of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$. Let $B,B'$ be noetherian $\mathbb{Z}_p$-algebras in which $p$ is nilpotent, $\psi:O\to B$, $\psi':O\to B'$ ring homomorphisms, and $f:B\to B'$ a $\mathbb{Z}_p$-algebra map with $f\circ\psi=\psi'$. Let $t$ be a rigidified object over $B$ (a formal $O_D$-module $X$, an integer $n$, a series $\rho$ over $B/pB$), admissible for $\iota,\psi$ ($X$ special, of height $4$, $\rho$ an isogeny of height $4n$). Let $Q$ be a Drinfeld datum over $B$ for $\mathcal{O}=\mathbb{Z}_p$, $K=\mathbb{Q}_p$, $\pi=p$, with $B$-linear isomorphisms $\sigma_0:Q.T_0\simeq \mathrm{Lie}^0 X$, $\sigma_1:Q.T_1\simeq \mathrm{Lie}^1 X$ making $(t,Q,\sigma_0,\sigma_1)$ a Cartier quadruple via $\iota,hc\Phi,r_\Phi,\psi$: $\rho$ is an $O_D$-homomorphism, $\sigma$ intertwines $\Pi_0,\Pi_1$ with the action of $\varpi$ on $\mathrm{Lie}\,X$, and at each prime the lattices $N_0,N_1$ are exactly the vectors admitting $\eta$-sections in degree $0$, resp. $1$, over a localisation away from an element outside that prime, with $u_0,u_1$ computed from those $\eta$-sections through $\sigma$. Let $(Q',\sigma_0',\sigma_1')$ be such a quadruple for $t$ base-changed along $f$ over $B'$, and let $\tau_0:Q.T_0\to Q'.T_0$, $\tau_1:Q.T_1\to Q'.T_1$ be $f$-semilinear maps whose images span $Q'.T_0$, $Q'.T_1$ over $B'$, satisfying $\tau_1\circ\Pi_0=\Pi_0'\circ\tau_0$ and $\tau_0\circ\Pi_1=\Pi_1'\circ\tau_1$, and such that for both indices the two Lie coordinates of $\sigma_i'(\tau_i s)$ equal $f$ applied to the corresponding coordinates of $\sigma_i(s)$. Then for $i=0,1$: for every prime $x'$ of $B'$ with image $x$ under $f$, every $v\in\mathbb{Q}_p^2$ lying in $N_i(x)$ and in $N_i'(x')$, every $t_0\in Q.T_i$ and $s\in B$ with $f(s)\notin x'$, the equality $u_{i,x}(1\otimes v)=t_0/s$ in the stalk of $T_i$ at $x$ implies $u_{i,x'}'(1\otimes v)=\tau_i(t_0)/f(s)$ in the stalk of $T_i'$ at $x'$.
--
--   This is the naturality, or base-change, compatibility for the two trivialisation maps $u_0,u_1$ attached to a Cartier quadruple in the Čerednik–Drinfeld uniformisation: the stalkwise description of $u$ over $B'$ is determined by that over $B$ through the semilinear comparison maps $\tau_0,\tau_1$. It is used in constructing the Lie-algebra comparison isomorphisms for isomorphic rigidified objects and in establishing that a Cartier quadruple over $B'$ is the base change of one over $B$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_u_baseChange.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open scoped TensorProduct

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[p] B'] (ψ' : O →+* B')
    (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B') (hf : (f : B →+* B').comp ψ = ψ')
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (σ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (σ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q σ₀ σ₁)
    (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (σ₀' : Q'.T₀ ≃ₗ[B'] ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ')))
    (σ₁' : Q'.T₁ ≃ₗ[B'] ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ')))
    (hQ' : (t.map (f : B →+* B')).IsCartierQuadrupleVia ι hcΦ rΦ ψ' Q' σ₀' σ₁')
    (τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀) (τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁)
    (hτ : (Submodule.span B' (Set.range τ₀) = ⊤) ∧ (Submodule.span B' (Set.range τ₁) = ⊤) ∧
      (∀ s, τ₁ (Q.Pi₀ s) = Q'.Pi₀ (τ₀ s)) ∧ (∀ s, τ₀ (Q.Pi₁ s) = Q'.Pi₁ (τ₁ s)))
    (hτσ : (∀ (s : Q.T₀) (i : Fin 2), ((σ₀' (τ₀ s) : ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) i =
          f (((σ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) i)) ∧
      (∀ (s : Q.T₁) (i : Fin 2), ((σ₁' (τ₁ s) : ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) i =
          f (((σ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) i))) :
    (∀ (x' : PrimeSpectrum B') (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ (DrinfeldDatum.pointUnder f x')) (hv' : v ∈ Q'.N₀ x')
    (tt : Q.T₀) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₀ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ (DrinfeldDatum.pointUnder f x')))) =
      LocalizedModule.mk tt (⟨s, hs⟩ : (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl) →
    Q'.u₀ x' ((1 : locRing B' x') ⊗ₜ[ℤ_[p]] (⟨v, hv'⟩ : ↥(Q'.N₀ x'))) =
      LocalizedModule.mk (τ₀ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)) ∧
    (∀ (x' : PrimeSpectrum B') (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₁ (DrinfeldDatum.pointUnder f x')) (hv' : v ∈ Q'.N₁ x')
    (tt : Q.T₁) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₁ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ (DrinfeldDatum.pointUnder f x')))) =
      LocalizedModule.mk tt (⟨s, hs⟩ : (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl) →
    Q'.u₁ x' ((1 : locRing B' x') ⊗ₜ[ℤ_[p]] (⟨v, hv'⟩ : ↥(Q'.N₁ x'))) =
      LocalizedModule.mk (τ₁ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)) := by sorry
