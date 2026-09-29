-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_lift_fromNormalization_kummer_of_isAffineOpen
-- name    : AlgebraicGeometry.existsUnique_lift_fromNormalization_kummer_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/cf1b2c31-04b2-5ac8-a4ad-2f2b523037f5
-- title:
--   Kummer normalisation represents k-th roots on an affine chart
-- statement:
--   Let $X$ be an integral scheme whose stalks $\mathcal{O}_{X,x}$ are all integrally closed domains, and write $K = K(X)$ for its function field (the stalk at the generic point). Fix $k \in \mathbb{N}$ and $g \in K$, a nonempty affine open $V \subseteq X$ such that the image of $k$ in $\Gamma(X,V)$ is a unit, a unit $u \in \Gamma(X,V)$, and $h \in K$ with $h \neq 0$, subject to the requirement that for every $x \in V$ the germ of $u$ at $x$ has image $g/h^{k}$ in $K$. Put $A' = K[T]/(T^{k} - g)$, let $f_0 \colon \operatorname{Spec} A' \to X$ be the composite of $\operatorname{Spec}$ of $K \to A'$ with the canonical map $\operatorname{Spec}\mathcal{O}_{X,\eta} \to X$ at the generic point, and let $\pi \colon Y \to X$ be the normalisation of $X$ in $A'$ determined by $f_0$, with canonical map $\operatorname{Spec} A' \to Y$. Then for every section $T \in \Gamma(Y, \pi^{-1}V)$ whose image in $\Gamma(\operatorname{Spec} A', \cdot)$ is the restriction of the global section $h^{-1}\bar t$, where $\bar t$ is the class of $T$ in $A'$, the following holds: for every scheme $Z$, every morphism $z \colon Z \to X$ with $z^{-1}V = \top$, and every $\tau \in \Gamma(Z, \mathcal{O}_Z)$ whose restriction satisfies $\tau^{k} = z^{*}u$, there is a unique morphism $s \colon Z \to Y$ with $s$ followed by $\pi$ equal to $z$ and $s^{*}T = \tau$.
--
--   This is the functor-of-points form, over an affine chart, of the assertion that the Kummer covering $Y \to X$ attached to $T^{k} = g$ parametrises $k$-th roots of the unit $u$, the section $h^{-1}\bar t$ playing the role of the tautological root. It is used in the construction of the $\mu_k$-covering in [`AlgebraicGeometry.exists_root_fromNormalization_kummer_existsUnique_lift`](thm.html#AlgebraicGeometry.exists_root_fromNormalization_kummer_existsUnique_lift), and rests on the description of the integral closure in a Kummer algebra as a monogenic étale finite extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_lift_fromNormalization_kummer_of_isAffineOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.existsUnique_lift_fromNormalization_kummer_of_isAffineOpen
    {X : Scheme.{u}} [IsIntegral X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (g : X.functionField)
    (V : X.Opens) (hV : IsAffineOpen V) (hVne : Nonempty V) (hk : IsUnit ((k : ℕ) : Γ(X, V)))
    (u : Γ(X, V)) (hu : IsUnit u) (h : X.functionField) (hh : h ≠ 0)
    (hval : ∀ (x : X) (hx : x ∈ V),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hx u) = g / h ^ k) :
    let A' := AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)
    let f₀ := Spec.map (CommRingCat.ofHom (algebraMap X.functionField A')) ≫ X.fromSpecStalk (genericPoint X)
    let π := f₀.fromNormalization
    let Y := f₀.normalization
    ∀ T : Γ(Y, π ⁻¹ᵁ V),
      f₀.toNormalization.app (π ⁻¹ᵁ V) T =
        (Spec (CommRingCat.of A')).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (algebraMap X.functionField A' h⁻¹ * AdjoinRoot.root _)) →
      ∀ (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ V = ⊤ →
        ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ k = z.app V u →
          ∃! s : Z ⟶ Y, s ≫ π = z ∧ s.app (π ⁻¹ᵁ V) T = Z.presheaf.map (homOfLE le_top).op τ := by sorry
