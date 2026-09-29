-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_le_etaleCoordinates_cons_algebraMap_of_point
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_le_etaleCoordinates_cons_algebraMap_of_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/e9670d3e-e52d-5eda-a88c-93f2e311bb14
-- title:
--   Affine étale-coordinate chart at a point of a smooth scheme over a curve
-- statement:
--   Let $S_c$ be a commutative ring that is an integral domain and a $\mathbb{C}$-algebra of finite type, assume $S_c$ is a smooth $\mathbb{C}$-algebra and that $\Omega_{S_c/\mathbb{C}}$ has rank $1$ as an $S_c$-module, and fix $t \in S_c$. Let $f : G \to \operatorname{Spec} S_c$ be a morphism of schemes which is smooth of relative dimension $g$, let $\sigma_1 : S_c \to \mathbb{C}$ be a $\mathbb{C}$-algebra map such that $\ker(\sigma_1)\cdot\Omega_{S_c/\mathbb{C}} + S_c\,dt = \Omega_{S_c/\mathbb{C}}$, let $P_0 : \operatorname{Spec}\mathbb{C} \to G$ satisfy $P_0$ followed by $f$ equal to $\operatorname{Spec}\sigma_1$, and let $O$ be an open subscheme of $G$ whose preimage under $P_0$ is all of $\operatorname{Spec}\mathbb{C}$. Then there is an affine open $U \le O$ of $G$ whose preimage under $P_0$ is again everything, such that, giving $B := \Gamma(G,U)$ the $S_c$-algebra structure obtained from the ring map $S_c \cong \Gamma(\operatorname{Spec} S_c,\top) \to B$ induced by $f$ (the inverse of `Scheme.ΓSpecIso` followed by `f.appLE ⊤ U`) and the $\mathbb{C}$-algebra structure obtained in the same way from $f$ followed by $\operatorname{Spec}$ of $\mathbb{C} \to S_c$: these make $\mathbb{C} \to S_c \to B$ a scalar tower, $B$ is an integral domain, of finite type and smooth over $\mathbb{C}$, with $\operatorname{rank}_B \Omega_{B/\mathbb{C}} = g+1$; and there are a $\mathbb{C}$-algebra map $\chi_0 : B \to \mathbb{C}$ and $s : \mathrm{Fin}\,g \to B$ such that $\chi_0$ is evaluation at $P_0$ (i.e. $\chi_0 b$ is the image of $(P_0)^{\sharp}_{U,\top}(b)$ under `Scheme.ΓSpecIso`), $\chi_0$ restricted to $S_c$ equals $\sigma_1$, and $\ker(\chi_0)\cdot\Omega_{B/\mathbb{C}}$ together with the $B$-span of the differentials of the $(g+1)$-tuple $(t_B, s_0, \dots, s_{g-1})$, where $t_B$ is the image of $t$ in $B$, spans $\Omega_{B/\mathbb{C}}$.
--
--   This is the existence of an affine open neighbourhood of a point of a smooth scheme over a smooth affine curve on which a system of étale coordinates over $\mathbb{C}$ can be chosen with the pulled-back base coordinate $t$ as its first member; it packages the data needed to produce an analytic chart. It feeds the construction of relative analytic charts for sections over the base, in [`AlgebraicGeometry.SmoothOfRelativeDimension.exists_relChart_differentiableOn_appLE_of_analyticChart`](thm.html#AlgebraicGeometry.SmoothOfRelativeDimension.exists_relChart_differentiableOn_appLE_of_analyticChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_le_etaleCoordinates_cons_algebraMap_of_point.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_KaehlerModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_le_etaleCoordinates_cons_algebraMap_of_point
    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1) (t : Sc)
    {G : Scheme.{0}} (f : G ⟶ Spec (CommRingCat.of Sc)) {g : ℕ} (hsm : SmoothOfRelativeDimension g f)
    (σ₁ : Sc →ₐ[ℂ] ℂ)
    (hdt₁ : (RingHom.ker σ₁.toRingHom) • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) ⊔
        Submodule.span Sc {KaehlerDifferential.D ℂ Sc t} = ⊤)
    (P₀ : Spec (CommRingCat.of ℂ) ⟶ G) (hP₀ : P₀ ≫ f = Spec.map (CommRingCat.ofHom σ₁.toRingHom))
    (O : G.Opens) (hO : ⊤ ≤ P₀ ⁻¹ᵁ O) :
    ∃ (U : G.Opens) (hU : IsAffineOpen U) (hUO : U ≤ O) (hP₀U : ⊤ ≤ P₀ ⁻¹ᵁ U),
      letI : Algebra Sc Γ(G, U) := f.sectionsAlgebra U
      letI : Algebra ℂ Γ(G, U) := (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))).sectionsAlgebra U
      IsScalarTower ℂ Sc Γ(G, U) ∧
      IsDomain Γ(G, U) ∧ Algebra.FiniteType ℂ Γ(G, U) ∧ Algebra.Smooth ℂ Γ(G, U) ∧
      Module.rank Γ(G, U) (KaehlerDifferential ℂ Γ(G, U)) = ((g + 1 : ℕ) : Cardinal) ∧
      ∃ (χ₀ : Γ(G, U) →ₐ[ℂ] ℂ) (s : Fin g → Γ(G, U)),
        (∀ b : Γ(G, U), χ₀ b = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P₀.appLE U ⊤ hP₀U) b)) ∧
        (∀ a : Sc, χ₀ (algebraMap Sc Γ(G, U) a) = σ₁ a) ∧
        (RingHom.ker χ₀.toRingHom) • (⊤ : Submodule Γ(G, U) (KaehlerDifferential ℂ Γ(G, U))) ⊔
          Submodule.span Γ(G, U) (Set.range fun i : Fin (g + 1) =>
            KaehlerDifferential.D ℂ Γ(G, U) ((Fin.cons (algebraMap Sc Γ(G, U) t) s : Fin (g + 1) → Γ(G, U)) i)) = ⊤ := by sorry
