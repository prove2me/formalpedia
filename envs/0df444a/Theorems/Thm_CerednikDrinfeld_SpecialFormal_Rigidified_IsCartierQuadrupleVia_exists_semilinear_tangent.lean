-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_semilinear_tangent
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_semilinear_tangent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/2191345f-0e0a-577b-a592-a234088cc846
-- title:
--   Semilinear tangent maps under base change of Cartier quadruples
-- statement:
--   Fix a prime $p$, a commutative ring $O$ and a ring homomorphism $\iota\colon W(\mathbb{F}_{p^2})\to O$, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $O/pO$ which is special for $\bar\jmath=\iota$ followed by reduction (its tangent space splits into the $\bar\jmath$- and $\bar\jmath\circ\mathrm{Frob}$-eigenparts, both invertible) and has height $4$; assume the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary, and let $r_\Phi\colon(\mathbb{Z}_p^2)\to N(\Phi)$ be an additive map which, for every canonical $L$-map $L$ on the graded Cartier module data of $\Phi$, maps all of its source bijectively onto the degree-$0$ $\eta$-piece $\mathrm{etaPiece}\,L\,0$. Let $B$, $B'$ be noetherian $\mathbb{Z}_p$-algebras in which $p$ is nilpotent, with $\psi\colon O\to B$, $\psi'\colon O\to B'$, and $f\colon B\to B'$ a $\mathbb{Z}_p$-algebra map with $f\circ\psi=\psi'$. Let $t$ be a rigidified triple over $B$ (a formal $O_D$-module $t.X$, an integer $n$, a series $\rho$ over $B/pB$), admissible for $(\iota,\psi)$. Let $Q$ be a Drinfeld datum over $B$ for $\pi=p$ and $K=\mathbb{Q}_p$, with $B$-linear identifications $\sigma_0\colon Q.T_0\cong \mathrm{Lie}_0(t.X)$, $\sigma_1\colon Q.T_1\cong\mathrm{Lie}_1(t.X)$ satisfying `IsCartierQuadrupleVia` (namely: $\rho$ is an $O_D$-module homomorphism; $\Pi_0,\Pi_1$ correspond under $\sigma_0,\sigma_1$ to the linear part of $\varpi$ on the tangent space; and at each prime $x$ of $B$ the lattices $N_0(x),N_1(x)$ are exactly the vectors realised by $\eta$-sections of the graded Cartier module data of $t$ over localisations of $B$ away from elements outside $x$, compatibly with $u_0,u_1$ and the $\sigma_i$). Let $Q'$, $\sigma_0'$, $\sigma_1'$ be such data for the base change $t\otimes_B B'$. Then there exist $f$-semilinear maps $\tau_0\colon Q.T_0\to Q'.T_0$ and $\tau_1\colon Q.T_1\to Q'.T_1$ whose ranges generate $Q'.T_0$, respectively $Q'.T_1$, over $B'$, which satisfy $\tau_1\circ\Pi_0=\Pi_0'\circ\tau_0$ and $\tau_0\circ\Pi_1=\Pi_1'\circ\tau_1$, and which are compatible with the tangent identifications coordinatewise: for $i\in\{0,1\}$ and each $s$, the coordinates of $\sigma_i'(\tau_i s)$ in $\mathrm{Lie}(t.X\otimes_BB')=(B')^2$ are the images under $f$ of the coordinates of $\sigma_i(s)$.
--
--   This is the tangent-space half of the base-change (naturality) statement for Cartier quadruples in the Čerednik–Drinfeld uniformisation: the invertible modules $T_0,T_1$ of a Drinfeld datum attached to a rigidified special formal module are computed from the graded tangent pieces, and hence transform semilinearly along $f\colon B\to B'$. It is used in the construction of the base-change isomorphism of Drinfeld data and in the proof that the associated Cartier module data form a base change along $f$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_semilinear_tangent.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_semilinear_tangent
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
    (hQ' : (t.map (f : B →+* B')).IsCartierQuadrupleVia ι hcΦ rΦ ψ' Q' σ₀' σ₁') :
    ∃ (τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀) (τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁),
      (Submodule.span B' (Set.range τ₀) = ⊤) ∧ (Submodule.span B' (Set.range τ₁) = ⊤) ∧
      (∀ s, τ₁ (Q.Pi₀ s) = Q'.Pi₀ (τ₀ s)) ∧ (∀ s, τ₀ (Q.Pi₁ s) = Q'.Pi₁ (τ₁ s)) ∧
      (∀ (s : Q.T₀) (i : Fin 2), ((σ₀' (τ₀ s) : ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) i =
          f (((σ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) i)) ∧
      (∀ (s : Q.T₁) (i : Fin 2), ((σ₁' (τ₁ s) : ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) i =
          f (((σ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) i)) := by sorry
