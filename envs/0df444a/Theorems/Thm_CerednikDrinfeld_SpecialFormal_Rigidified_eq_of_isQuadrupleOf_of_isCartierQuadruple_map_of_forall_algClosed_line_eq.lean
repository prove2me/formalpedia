-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isQuadrupleOf_of_isCartierQuadruple_map_of_forall_algClosed_line_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isQuadrupleOf_of_isCartierQuadruple_map_of_forall_algClosed_line_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/74187de9-5759-5ba0-8c42-91c556f63b8c
-- title:
--   Pulled-back edge family recovers the standard-chart Deligne datum
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring map $\iota : W(\mathbb F_{p^2}) \to W(k)$ and a formal $O_D$-module $\Phi$ over $W(k)/pW(k)$, and write $\bar\jmath$ for the composite of $\iota$ with reduction modulo $p$. Assume: $\Phi$ is special for $\bar\jmath$ (its $\bar\jmath$-weight-$0$ and weight-$1$ parts of the Lie module are complementary and invertible), $\Phi$ has height $4$, the weight-$0$ part of the Lie module is killed by the operator induced by $\varpi$, the graded pieces of degree $0$ and $1$ of the Cartier module of $\Phi$ (the eigenspaces for the Teichmüller action with eigenvalue $\bar\jmath(\cdot)^{p^n}$, $n=0,1$) are complementary, as witnessed by `hcΦ`, and an additive map $r_\Phi : (\mathbb Z_p)^2 \to$ `NMod` of the associated graded Cartier module datum is given which, for every canonical $L$-map $L$, maps $(\mathbb Z_p)^2$ bijectively onto the degree-$0$ eta piece of $L$. Let $g \in \mathrm{GL}_2(\mathbb Q_p)$ have matrix $\mathrm{diag}(p,1)$, let $E$ be the edge chart ring over $W(k)/pW(k)$ with uniformiser $0$ and parameter $p$ (the localisation of $(W(k)/p)[\xi,\eta]/(\xi\eta)$ at the discriminant), with structure map $\psi_E : W(k) \to E$ obtained from reduction followed by the structure morphism, and let $t_E = (X,n,\rho)$ be a rigidified object over $E$ which is admissible for $\iota$ and $\psi_E$. Assume further the geometric hypothesis: for every algebraically closed field $\Omega$ that is a $\mathbb Z_p$-algebra and every ring map $y_\Omega : E \to \Omega$ there are a Drinfeld datum $Q$ and a Deligne datum $d$ over $\Omega$ for $(\mathbb Z_p, \mathbb Q_p, p)$ such that $Q$ is a Cartier quadruple of the base change of $t_E$ along $y_\Omega$ (relative to $\iota$, `hcΦ`, $r_\Phi$ and $y_\Omega \circ \psi_E$), $Q$ is the quadruple of $d$, and the lines of $d$ at the standard lattice and at $g$ applied to it are the spans of $y_\Omega(\xi)\otimes e_0 + 1\otimes e_1$ and, after the base-change isomorphism, of $1\otimes e_0 + y_\Omega(\eta)\otimes e_1$. Then for every Noetherian commutative $\mathbb Z_p$-algebra $B$, every ring map $\psi : W(k) \to B$ with $p$ nilpotent in $B$ and $(p : B) = 0$, every $\mathbb Z_p$-algebra map $x$ from the standard edge chart ring $\mathrm{chartERing}\ \mathbb Z_p\ p\ p$ to $B$ and every Deligne datum $d$ over $B$ which satisfies the edge nondegeneracy condition at every prime of $B$ for the pair $(g\cdot L_{\mathrm{std}}, L_{\mathrm{std}})$ and whose lines at $L_{\mathrm{std}}$ and at $g\cdot L_{\mathrm{std}}$ are given by the same two explicit spans with $x(\xi)$, $x(\eta)$ in place of $y_\Omega(\xi)$, $y_\Omega(\eta)$: whenever $y : E \to B$ is a ring map with $y\circ\psi_E = \psi$, $y(\xi) = x(\xi)$ and $y(\eta) = x(\eta)$, and $Q$ is a Drinfeld datum over $B$ which is a Cartier quadruple of the base change of $t_E$ along $y$ (relative to $\iota$, `hcΦ`, $r_\Phi$, $\psi$) and is the quadruple of a Deligne datum $d'$, then $d' = d$.
--
--   This is the rigidity step in the proof that the standard edge chart is hit by the moduli of special formal modules in the Čerednik–Drinfeld uniformisation: the Deligne datum attached to a rigidified object over the edge ring is pinned down by its values at geometric points, because the edge ring over an algebraically closed residue field is reduced, and then transported along a point $y$ of that ring. It is used by [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_line_eq_of_charP`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_line_eq_of_charP), which produces an admissible rigidified object with prescribed Deligne datum over a characteristic-$p$ base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isQuadrupleOf_of_isCartierQuadruple_map_of_forall_algClosed_line_eq.lean

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
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isQuadrupleOf_of_isCartierQuadruple_map_of_forall_algClosed_line_eq
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
(tE : Rigidified p Φ (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))
(htE : tE.IsAdmissible ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))
(hgeo :
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (yΩ : EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* Ω),
        ∃ (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω),
          (tE.map yΩ).IsCartierQuadruple ι hcΦ rΦ (yΩ.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
        (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) Q ∧ Q.IsQuadrupleOf d ∧
          d.line (stdFullLattice ℚ_[p]) =
            Submodule.span Ω {(yΩ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]]
              stdBasisVec ℚ_[p] 0 + (1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} ∧
          d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
            (Submodule.span Ω {(1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 +
              (yΩ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
              (actBaseChange Ω g (stdFullLattice ℚ_[p])).toLinearMap)
    :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
      (hB : IsNilpotent (p : B)) (hp0 : (p : B) = 0)
      (x : chartERing ℤ_[p] (p : ℤ_[p]) p →ₐ[ℤ_[p]] B)
      (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B),
      d.InEdgeChart (p : ℤ_[p]) (FullLattice.act g (stdFullLattice ℚ_[p])) (stdFullLattice ℚ_[p]) →
      d.line (stdFullLattice ℚ_[p]) =
        Submodule.span B {(x (chartERing.ξ ℤ_[p] (p : ℤ_[p]) p)) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : B) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} →
      d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
        (Submodule.span B {(1 : B) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (x (chartERing.η ℤ_[p] (p : ℤ_[p]) p)) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
          (actBaseChange B g (stdFullLattice ℚ_[p])).toLinearMap →
      ∀ (y : EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* B),
        y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = ψ →
        y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = x (chartERing.ξ ℤ_[p] (p : ℤ_[p]) p) →
        y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = x (chartERing.η ℤ_[p] (p : ℤ_[p]) p) →
        ∀ (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (d' : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B),
          (tE.map y).IsCartierQuadruple ι hcΦ rΦ ψ Q → Q.IsQuadrupleOf d' → d' = d := by sorry
