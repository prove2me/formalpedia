-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_via_linearPart_of_isODHom_of_comp_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_via_linearPart_of_isODHom_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/9f776005-3b2c-58b3-a9f8-6800151f765c
-- title:
--   Transport of a Cartier quadruple along an isomorphism of rigidified modules
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring homomorphism $\iota:\mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})\to O$, and a formal $\mathcal{O}_D$-module $\Phi$ over $O/pO$ which is special for $\bar\jmath=\iota$ followed by reduction (its zero and one Lie eigen-submodules are complementary and invertible) and has height $4$; assume the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary, with complement datum $hc_\Phi$, and let $r_\Phi:(\mathbb{Z}_p^2,+)\to N(\Phi)$ be an additive map which, for every canonical $L$-map $L$ on the associated graded Cartier module datum, maps all of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$. Let $B$ be a Noetherian $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi:O\to B$ a ring homomorphism, and $t=(X,n,\rho)$, $t'=(X',n',\rho')$ rigidified objects over $B$ that are admissible for $(\iota,\psi)$, i.e. $X$ is special for $\psi\circ\iota$ of height $4$ and $\rho$ is an isogeny of height $4n$ from $\Phi$ base-changed along $\psi$ to $X$ mod $p$, and likewise for $t'$. Let $u,w$ be two-variable power series tuples over $B$ that are $\mathcal{O}_D$-homomorphisms $X\to X'$ and $X'\to X$ (law homomorphisms commuting with the $\mathbb{Z}_{p^2}$-action and with $\varpi$), mutually inverse under substitution, and suppose that for some $m\in\mathbb{N}$ one has $[p^{m+n'}]_{X'}\circ\bar u\circ\rho=[p^{m+n}]_{X'}\circ\rho'$ modulo $p$, where $[p^k]$ denotes the action of $p^k\in\mathbb{Z}_{p^2}$. Let $Q$ be a Drinfeld datum over $B$ for $(\mathbb{Q}_p,p)$ and $\sigma_0:Q.T_0\cong\mathrm{Lie}^0X$, $\sigma_1:Q.T_1\cong\mathrm{Lie}^1X$ $B$-linear isomorphisms such that $Q$ is the Cartier quadruple of $t$ via $(\sigma_0,\sigma_1)$ in the sense of `IsCartierQuadrupleVia`: $\rho$ is an $\mathcal{O}_D$-homomorphism, the $\sigma_i$ intertwine $\Pi_0,\Pi_1$ with the linear part of $\varpi_X$, and at each prime $x$ of $B$ the lattices $N_0(x),N_1(x)$ consist exactly of the vectors realised by $\eta$-sections over suitable localisations away from $x$, compatibly with $u_0,u_1$ and the $\sigma_i$. Then there exist $B$-linear isomorphisms $\rho_0:Q.T_0\cong\mathrm{Lie}^0X'$ and $\rho_1:Q.T_1\cong\mathrm{Lie}^1X'$ making $Q$ the Cartier quadruple of $t'$ via $(\rho_0,\rho_1)$, and such that coordinatewise $\rho_i(s)=\mathrm{d}u\cdot\sigma_i(s)$ for all $s$, where $\mathrm{d}u$ is the $2\times2$ matrix of linear coefficients of $u$ acting on $\mathrm{Lie}\,X=B^2$.
--
--   This is the functoriality of the Cartier quadruple attached to a rigidified special formal $\mathcal{O}_D$-module under an isomorphism of rigidified objects, in the refined form that records the effect on the tangent identifications: transport along $u$ replaces $\sigma_i$ by $\mathrm{d}u\circ\sigma_i$. It is used in the construction of the equivalence between rigidified special formal $\mathcal{O}_D$-modules and Drinfeld data, where one must compare the quadruples attached to isomorphic objects and, in particular, in `exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_via_linearPart_of_isODHom_of_comp_eq.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_via_linearPart_of_isODHom_of_comp_eq
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
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (u w : Series B) (m : ℕ)
    (hu : FormalODModule.IsODHom t.X t'.X u) (hw : FormalODModule.IsODHom t'.X t.X w)
    (hwu : w.comp u = Series.id B) (huw : u.comp w = Series.id B)
    (hρ : (t'.Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp ((u.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ)
      = (t'.Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp t'.ρ)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (σ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (σ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q σ₀ σ₁) :
    ∃ (ρ₀ : Q.T₀ ≃ₗ[B] ↥(t'.X.lieZero (structureMap ι ψ)))
      (ρ₁ : Q.T₁ ≃ₗ[B] ↥(t'.X.lieOne (structureMap ι ψ))),
      t'.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q ρ₀ ρ₁ ∧
      (∀ (s : Q.T₀) (i : Fin 2), ((ρ₀ s : ↥(t'.X.lieZero (structureMap ι ψ))) : t'.X.Lie) i =
          (Matrix.mulVecLin (MvFormalGroup.linearPart u) ((σ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie)) i) ∧
      (∀ (s : Q.T₁) (i : Fin 2), ((ρ₁ s : ↥(t'.X.lieOne (structureMap ι ψ))) : t'.X.Lie) i =
          (Matrix.mulVecLin (MvFormalGroup.linearPart u) ((σ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie)) i) := by sorry
