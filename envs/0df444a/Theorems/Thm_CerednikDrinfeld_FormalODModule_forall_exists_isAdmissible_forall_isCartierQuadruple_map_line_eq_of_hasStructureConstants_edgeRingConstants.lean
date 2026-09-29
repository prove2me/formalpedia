-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_forall_exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_of_hasStructureConstants_edgeRingConstants
-- name    : CerednikDrinfeld.FormalODModule.forall_exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_of_hasStructureConstants_edgeRingConstants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/c10d7cda-73c8-55d4-9fce-f0257ee33e9e
-- title:
--   Rigidification of the explicit edge family with standard Drinfeld lines
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ over $W(k)/pW(k)$, with $\bar{\jmath}$ the composite of $\iota$ with reduction mod $p$. Assume: $\Phi$ is special for $\bar{\jmath}$ (its weight-$0$ and weight-$1$ Lie submodules are complementary and both invertible); $\Phi$ has height $4$, i.e. multiplication by $p$ has kernel of degree $p^4$; the weight-$0$ Lie submodule lies in the kernel of the linear part of $\varpi$; the graded pieces of degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary, via a witness $h_{c\Phi}$; and $r_\Phi$ is an additive map $\mathbb{Z}_p^2 \to \mathrm{NMod}$ of the associated graded Cartier module data which, for every canonical $L$-map $L$, is a bijection from all of $\mathbb{Z}_p^2$ onto the degree-$0$ $\eta$-piece of $L$. Let $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ be the diagonal matrix $\mathrm{diag}(p,1)$. Write $E$ for the standard edge-chart ring $\mathrm{edgeRingCharP}$ over $W(k)/pW(k)$, with its elements $\xi,\eta$, and $\psi \colon W(k) \to E$ for reduction followed by the structural algebra map. The conclusion asserts: for every formal $\mathcal{O}_D$-module $X$ over $E$ and every pair $\gamma = (\gamma_0,\gamma_1)$ of elements of the Cartier module of $X$ such that $\gamma$ is a homogeneous $V$-basis for $\psi \circ \iota$ (each $\gamma_i$ lies in the graded piece of degree $i$ and the tangent matrix of $\gamma$ has unit determinant), $\gamma$ has structure constants the edge constants $\mathrm{edgeRingConstants}$ built from $\xi$ and $\eta$, and $X$ is special of height $4$, there exist $n \in \mathbb{N}$ and a $2$-tuple of power series $\rho$ over $E/pE$ such that the rigidified triple $(X,n,\rho)$ (with base point $\Phi$) is admissible for $(\iota,\psi)$, i.e. $X$ is special, of height $4$, and $\rho$ is an isogeny of height $4n$ from the base change of $\Phi$ to the reduction of $X$; and, for every algebraically closed field $\Omega$ which is a $\mathbb{Z}_p$-algebra and every ring homomorphism $y \colon E \to \Omega$, there are a Drinfeld datum $Q$ over $\Omega$ for the uniformiser $p \in \mathbb{Z}_p \subset \mathbb{Q}_p$ and a Deligne datum $d$ over $\Omega$ with: the base change of $(X,n,\rho)$ along $y$ is a Cartier quadruple for the data $(\iota,h_{c\Phi},r_\Phi, y\circ\psi)$ and $Q$; $Q$ is the Drinfeld quadruple of $d$; and the two lines of $d$ are the explicit ones, namely $d$ at the standard full lattice is the $\Omega$-span of $y(\xi) \otimes e_0 + 1 \otimes e_1$, while $d$ at the $g$-translate of the standard full lattice is the image, under the base-change isomorphism induced by $g$, of the $\Omega$-span of $1 \otimes e_0 + y(\eta) \otimes e_1$.
--
--   This is the Cartier-theoretic input to Drinfeld's local uniformisation: it says that the formal $\mathcal{O}_D$-module over the standard edge chart determined by the edge structure constants can be rigidified with respect to a fixed special $\Phi$ of height $4$, and that its associated Drinfeld quadruple at every geometric point is the quadruple of the Deligne datum whose lines over the standard lattice and its $\mathrm{diag}(p,1)$-translate are the two explicit coordinate lines. It is used in the construction of the edge family over $\mathrm{edgeRingCharP}$ that establishes surjectivity of the period map on edges.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_forall_exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_of_hasStructureConstants_edgeRingConstants.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.forall_exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_of_hasStructureConstants_edgeRingConstants
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
(hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
    :
    ∀ (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F),
      X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
        (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ →
      X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))) →
      X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
        (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) → X.HasHeight 4 →
    ∃ (n : ℕ) (ρ : Series ((EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) ⧸ pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))),
      (Rigidified.mk (Φ := Φ) X n ρ).IsAdmissible ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
        (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (y : EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* Ω),
        ∃ (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω),
          ((Rigidified.mk (Φ := Φ) X n ρ).map y).IsCartierQuadruple ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
        (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) Q ∧ Q.IsQuadrupleOf d ∧
          d.line (stdFullLattice ℚ_[p]) =
            Submodule.span Ω {(y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]]
              stdBasisVec ℚ_[p] 0 + (1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} ∧
          d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
            (Submodule.span Ω {(1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 +
              (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
              (actBaseChange Ω g (stdFullLattice ℚ_[p])).toLinearMap := by sorry
