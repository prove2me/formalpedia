-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
-- name    : AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/7e6fee0a-6ab1-5893-87c6-990433eebe23
-- title:
--   Maps out of a flat reduced scheme determined by geometric generic points
-- statement:
--   Let $R$ be a commutative domain, $K$ a field that is a fraction field of $R$, and $\Omega$ an algebraically closed field carrying compatible $R$- and $K$-algebra structures (so that $R \to K \to \Omega$ is a tower). Let $X$ and $Y$ be schemes with structure morphisms $f : X \to \operatorname{Spec} R$ and $g : Y \to \operatorname{Spec} R$, where $f$ is flat and locally of finite presentation, $X$ is reduced, and $g$ is separated. Let $\varphi, \psi : X \to Y$ be two morphisms over $\operatorname{Spec} R$, i.e. $\varphi$ followed by $g$ and $\psi$ followed by $g$ both equal $f$. Assume that for every $\Omega$-valued point $x : \operatorname{Spec} \Omega \to X$ whose composite with $f$ is the morphism $\operatorname{Spec} \Omega \to \operatorname{Spec} R$ induced by the structure map $R \to \Omega$, the composites of $x$ with $\varphi$ and with $\psi$ agree. Then $\varphi = \psi$. Since $R \to \Omega$ is injective, the condition on $x$ says precisely that $x$ factors through the generic fibre, so the hypothesis is agreement on the geometric points of $X_K$ with values in $\Omega$.
--
--   This is the standard rigidity statement that a morphism from a flat, reduced scheme of finite presentation over a domain into a separated scheme is determined by its effect on the $\Omega$-valued points of the generic fibre. It is used in the form 'a morphism of a smooth group scheme over a discrete valuation ring is determined by what it does on the geometric points of the generic fibre', and is invoked for the smooth case in [`AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated`](thm.html#AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated) and in the descent and Hecke-operator computations on Néron models over modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [Flat f] [LocallyOfFinitePresentation f] [IsReduced X] [IsSeparated g]
    (φ ψ : X ⟶ Y) (hφ : φ ≫ g = f) (hψ : ψ ≫ g = f)
    (h : ∀ x : Spec (CommRingCat.of Ω) ⟶ X,
      x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) → x ≫ φ = x ≫ ψ) :
    φ = ψ := by sorry
