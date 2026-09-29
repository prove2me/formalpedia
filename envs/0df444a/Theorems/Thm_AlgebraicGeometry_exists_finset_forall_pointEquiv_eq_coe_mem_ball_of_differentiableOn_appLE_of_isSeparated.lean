-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated
-- name    : AlgebraicGeometry.exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/37e6de29-ca4e-5906-8d64-edbd1caafdad
-- title:
--   Section values detect the uniformising ball of a point
-- statement:
--   Let $G$ be a scheme and $f : G \to \operatorname{Spec}\mathbb{C}$ a separated morphism, and let $g$ be a natural number. A $\mathbb{C}$-point of $G$ is here an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f`, that is, a morphism $P : \operatorname{Spec}\mathbb{C} \to G$ together with the condition that $P$ followed by $f$ is the identity of $\operatorname{Spec}\mathbb{C}$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{C}^g = (\mathrm{Fin}\,g \to \mathbb{C})$ and let $e$ be a bijection from the set of such $\mathbb{C}$-points onto $\mathbb{C}^g/\Lambda$ (the quotient by the additive subgroup underlying $\Lambda$). Assume (hL1) that $\Lambda$ is the $\mathbb{Z}$-span of the range of some $\mathbb{R}$-basis of $\mathbb{C}^g$ indexed by $\mathrm{Fin}(2g)$, so that $\Lambda$ is a full lattice; and assume (hAN) that for every open $U \subseteq G$ and every section $\varphi \in \Gamma(G,U)$ the set $S_U$ of those $v \in \mathbb{C}^g$ for which the point $e^{-1}([v])$ factors through $U$ (i.e. the preimage of $U$ under $e^{-1}([v])$ is the whole of $\operatorname{Spec}\mathbb{C}$) is open, and there is a function $F : \mathbb{C}^g \to \mathbb{C}$, complex differentiable on $S_U$, whose value at each $v \in S_U$ is the value of $\varphi$ at $e^{-1}([v])$, obtained by restricting $\varphi$ along `appLE` and identifying $\Gamma(\operatorname{Spec}\mathbb{C}, \top)$ with $\mathbb{C}$ via `Scheme.ΓSpecIso`. The conclusion is: for every $v_0 \in \mathbb{C}^g$ and every real $r > 0$ there exist an open $U \subseteq G$ through which $e^{-1}([v_0])$ factors, a finite set $fs$ of sections in $\Gamma(G,U)$ and a real $\varepsilon > 0$ such that for every $\mathbb{C}$-point $P$ factoring through $U$, if $|\varphi(P) - \varphi(e^{-1}([v_0]))| < \varepsilon$ for all $\varphi \in fs$ (values taken as above), then $e(P) = [w]$ for some $w$ in the open ball of radius $r$ about $v_0$.
--
--   This is the comparison of topologies underlying an analytic uniformisation $G(\mathbb{C}) \cong \mathbb{C}^g/\Lambda$: neighbourhoods of a point cut out by finitely many section values and a single tolerance $\varepsilon$ are carried into arbitrarily small balls of the uniformising parameter, the converse direction to the holomorphy clause (hAN). It is used in the construction of differentiable lifts along curve models and in the analytic characterisation of lattice maps in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology

theorem AlgebraicGeometry.exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} [IsSeparated f] {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup))
    (hL1 : ∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), Λ = Submodule.span ℤ (Set.range b₀))
    (hAN : ∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ))) :
    ∀ (v₀ : Fin g → ℂ) (r : ℝ), 0 < r →
      ∃ (U : G.Opens) (fs : Finset (Γ(G, U))) (ε : ℝ) (h₀ : ⊤ ≤ (e.symm (v₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U), 0 < ε ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
          (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((e.symm (v₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h₀) φ)‖ < ε) →
          ∃ w ∈ Metric.ball v₀ r, e P = (w : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) := by sorry
