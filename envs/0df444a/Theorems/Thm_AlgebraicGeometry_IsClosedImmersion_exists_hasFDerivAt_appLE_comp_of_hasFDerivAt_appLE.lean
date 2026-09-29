-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE
-- name    : AlgebraicGeometry.IsClosedImmersion.exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/1b9cc2fc-145e-5cb9-85d0-4e500088fd0a
-- title:
--   Local coordinates of a ℂ-point family push forward along a closed immersion
-- statement:
--   Let $g : X \to Y$ be a closed immersion of schemes (over the base universe $0$), let $\pi$ assign to each $v \in \mathbb{C}^2$ a morphism $\pi v : \operatorname{Spec}\mathbb{C} \to X$, and let $v_0 \in \mathbb{C}^2$. Assume the Zariski-continuity hypothesis `hcont`: for every open $W \subseteq X$ with $\pi v_0 ^{-1}W = \top$ there is $\varepsilon' > 0$ such that $(\pi v)^{-1}W = \top$ for all $v$ in the ball $B(v_0,\varepsilon')$. Assume further given an open $U \subseteq X$, sections $f_1, f_2 \in \Gamma(X, U)$, a real $\varepsilon > 0$, a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^2$ and a map $F : \mathbb{C}^2 \to \mathbb{C}^2$ such that: $(\pi v)^{-1}U = \top$ for all $v \in B(v_0,\varepsilon)$; for every such $v$ the value $F v$ is the pair obtained by applying $(\pi v)^{\sharp}$ on sections from $U$ to the whole of $\operatorname{Spec}\mathbb{C}$ (via `Scheme.Hom.appLE`) to $f_1$ and $f_2$ and transporting along the canonical isomorphism $\Gamma(\operatorname{Spec}\mathbb{C}) \cong \mathbb{C}$; and $F$ has Fréchet derivative $D$ at $v_0$. The conclusion asserts the existence of an open $V \subseteq Y$, sections $f_2', f_3' \in \Gamma(Y, V)$, a real $\varepsilon' > 0$ and a map $F' : \mathbb{C}^2 \to \mathbb{C}^2$ with $\varepsilon' > 0$, with $(\pi v \text{ followed by } g)^{-1}V = \top$ for all $v \in B(v_0,\varepsilon')$, with $F' v$ equal to the pair of values of $f_2', f_3'$ pulled back along $\pi v$ followed by $g$ for such $v$, and with $F'$ having the same derivative $D$ at $v_0$.
--
--   This is the statement that a family of $\mathbb{C}$-points equipped with local analytic coordinates cut out by two regular functions retains such coordinates, with the same derivative, after composition with a closed immersion. It is used in the construction of the local uniformisation of a family of fake elliptic curves, where coordinates on a moduli scheme are transported to an ambient scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology

theorem AlgebraicGeometry.IsClosedImmersion.exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE
    {X Y : Scheme.{0}} (g : X ⟶ Y) [IsClosedImmersion g]
    (π : (Fin 2 → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ X)) (v₀ : Fin 2 → ℂ)

    (hcont : ∀ W : X.Opens, ⊤ ≤ (π v₀) ⁻¹ᵁ W → ∃ ε' : ℝ, 0 < ε' ∧ ∀ v ∈ Metric.ball v₀ ε', ⊤ ≤ (π v) ⁻¹ᵁ W)

    (U : X.Opens) (f₁ f₂ : Γ(X, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ)) (F : (Fin 2 → ℂ) → (Fin 2 → ℂ))
    (hε : 0 < ε) (hU : ∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (π v) ⁻¹ᵁ U)
    (hF : ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (π v) ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
      F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v).appLE U ⊤ h) f₁), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v).appLE U ⊤ h) f₂)])
    (hD : HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀) :
    ∃ (V : Y.Opens) (f₂' f₃' : Γ(Y, V)) (ε' : ℝ) (F' : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
      0 < ε' ∧
      (∀ v ∈ Metric.ball v₀ ε', ⊤ ≤ (π v ≫ g) ⁻¹ᵁ V) ∧
      (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (π v ≫ g) ⁻¹ᵁ V), v ∈ Metric.ball v₀ ε' →
        F' v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v ≫ g).appLE V ⊤ h) f₂'), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v ≫ g).appLE V ⊤ h) f₃')]) ∧
      HasFDerivAt F' (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀ := by sorry
