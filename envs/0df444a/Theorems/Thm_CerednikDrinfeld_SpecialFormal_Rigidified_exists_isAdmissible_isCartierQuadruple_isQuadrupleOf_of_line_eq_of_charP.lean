-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_line_eq_of_charP
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_line_eq_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/4b97cc03-4a6d-5922-a090-06aceeaa6cbe
-- title:
--   Drinfeld surjectivity on the standard edge chart in characteristic p
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota \colon W(\mathbb F_{p^2}) \to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$, and write $\bar\iota$ for $\iota$ followed by reduction modulo $pW(k)$. Assume: $\Phi$ is special for $\bar\iota$, i.e. the Lie subspaces $\mathrm{lieZero}$ and $\mathrm{lieOne}$ are complementary and each invertible; $\Phi$ has height $4$, i.e. the series giving the action of $p$ has kernel of degree $p^4$; $\mathrm{lieZero}(\bar\iota) \subseteq \ker(\mathrm{lieVarpi})$; the graded pieces of index $0$ and $1$ of the Cartier module of $\Phi$ relative to $\bar\iota$ are complementary (hypothesis $hc_\Phi$); and there is an additive map $r_\Phi \colon \mathbb Z_p^2 \to \mathrm{NMod}$ of the associated graded Cartier module data which, for every canonical $L$-map $L$, maps $\mathbb Z_p^2$ bijectively onto the $\eta$-piece of index $0$ attached to $L$. Let $g \in \mathrm{GL}_2(\mathbb Q_p)$ be $\mathrm{diag}(p,1)$. The assertion is then: for every Noetherian commutative $\mathbb Z_p$-algebra $B$, every ring homomorphism $\psi \colon W(k) \to B$, with $p$ nilpotent in $B$ and indeed $p = 0$ in $B$, every $\mathbb Z_p$-algebra map $x$ from the standard edge-chart ring $\mathrm{chartERing}\,\mathbb Z_p\,p\,p$ (the localisation of $\mathbb Z_p[\xi,\eta]/(\xi\eta - p)$ away from the discriminant) to $B$, and every Deligne datum $d$ over $B$ for $\pi = p$, $K = \mathbb Q_p$: if $d$ is edge-nondegenerate at every prime of $B$ for the pair $(g\cdot\mathbb Z_p^2,\ \mathbb Z_p^2)$, if $d$'s line at the standard lattice is the $B$-span of $x(\xi)\otimes e_0 + 1\otimes e_1$, and if $d$'s line at $g\cdot\mathbb Z_p^2$ is the image under the base-changed action of $g$ of the $B$-span of $1\otimes e_0 + x(\eta)\otimes e_1$, then there exist a rigidified object $t$ over $B$ (a formal $\mathcal O_D$-module $t.X$ over $B$, an integer $t.n$, and a series $t.\rho$ over $B/pB$) and a Drinfeld datum $Q$ over $B$ such that $t$ is admissible for $(\iota,\psi)$ — $t.X$ special, of height $4$, with $t.\rho$ an isogeny of height $4\,t.n$ from the reduction of $\Phi$ to the reduction of $t.X$ — such that $Q$ is the Cartier quadruple of $t$ relative to $(\iota, hc_\Phi, r_\Phi, \psi)$, and such that $Q$ is a quadruple of $d$.
--
--   This is the form taken by Drinfeld's surjectivity statement inside a single edge chart of the formal upper half-plane in characteristic $p$: a Deligne datum whose two lines are given explicitly by a point $x$ of the standard edge-chart ring arises from an admissible rigidified special formal $\mathcal O_D$-module together with its Cartier quadruple. Combined with the covering of the formal upper half-plane by $\mathrm{GL}_2(\mathbb Q_p)$-translates of the standard chart, it yields the Zariski-local version of the comparison, and it is used for precisely that purpose.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_line_eq_of_charP.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_line_eq_of_charP
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
      ∃ (t : Rigidified p Φ B) (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B),
        t.IsAdmissible ι ψ ∧ t.IsCartierQuadruple ι hcΦ rΦ ψ Q ∧ Q.IsQuadrupleOf d := by sorry
