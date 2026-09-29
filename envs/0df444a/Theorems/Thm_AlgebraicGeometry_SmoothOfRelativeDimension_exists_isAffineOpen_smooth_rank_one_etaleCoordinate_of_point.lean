-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/679850e4-74bb-59ec-bbac-5bb875c7eed8
-- title:
--   Affine neighbourhood with étale coordinate on a smooth complex curve
-- statement:
--   Let $M$ be a scheme, $\pi_M : M \to \operatorname{Spec}\mathbb{C}$ a morphism that is smooth of relative dimension $1$, and $\sigma : \operatorname{Spec}\mathbb{C} \to M$ a section of $\pi_M$, i.e. $\sigma$ followed by $\pi_M$ is the identity. Then there are an open subscheme $U \subseteq M$ that is affine, with $\sigma^{-1}(U) = \top$ (so $\sigma$ factors through $U$), and an $\mathbb{C}$-algebra structure on the sections $S := \Gamma(U, \mathcal{O}_M)$ whose structure map sends $z \in \mathbb{C}$ to the restriction to $U$ of the image of $z$ under $\Gamma$ applied to $\pi_M$ on global sections (read through the isomorphism $\Gamma(\operatorname{Spec}\mathbb{C}) \cong \mathbb{C}$), such that: $S$ is a domain, of finite type over $\mathbb{C}$, smooth over $\mathbb{C}$, the $S$-module $\Omega_{S/\mathbb{C}}$ of Kähler differentials has rank $1$, and there exist an $\mathbb{C}$-algebra homomorphism $\sigma_0 : S \to \mathbb{C}$, given by evaluation at $\sigma$ (the map induced by $\sigma$ on sections over $U$, composed with $\Gamma(\operatorname{Spec}\mathbb{C}) \cong \mathbb{C}$), and an element $t \in S$ with $\mathrm{d}t \notin \ker(\sigma_0)\,\Omega_{S/\mathbb{C}}$.
--
--   This is the algebraic input for a local analytic coordinate on a smooth complex curve: the element $t$ is an étale coordinate at the point $\sigma$, since $\mathrm{d}t$ generates $\Omega_{S/\mathbb{C}}$ after localising at $\ker\sigma_0$. It supplies exactly the hypotheses of the analytic charting statement used to produce local holomorphic coordinates, and is invoked in the construction of period charts on Čerednik–Drinfeld quaternionic moduli schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ)) (hsm : SmoothOfRelativeDimension 1 πM)
    (σ : Spec (CommRingCat.of ℂ) ⟶ M) (hσ : σ ≫ πM = 𝟙 _) :
    ∃ (U : M.Opens) (hU : IsAffineOpen U) (hσU : ⊤ ≤ σ ⁻¹ᵁ U)
      (inst : Algebra ℂ ↑(M.presheaf.obj (op U))),

      (∀ z : ℂ, algebraMap ℂ ↑(M.presheaf.obj (op U)) z =
        (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          (πM.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom z))) ∧
      IsDomain ↑(M.presheaf.obj (op U)) ∧ Algebra.FiniteType ℂ ↑(M.presheaf.obj (op U)) ∧
      Algebra.Smooth ℂ ↑(M.presheaf.obj (op U)) ∧
      Module.rank ↑(M.presheaf.obj (op U)) (KaehlerDifferential ℂ ↑(M.presheaf.obj (op U))) = 1 ∧
      ∃ (σ₀ : ↑(M.presheaf.obj (op U)) →ₐ[ℂ] ℂ) (t : ↑(M.presheaf.obj (op U))),
        (∀ s : ↑(M.presheaf.obj (op U)),
          σ₀ s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((σ.appLE U ⊤ hσU).hom s)) ∧
        KaehlerDifferential.D ℂ ↑(M.presheaf.obj (op U)) t ∉
          (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule ↑(M.presheaf.obj (op U)) (KaehlerDifferential ℂ ↑(M.presheaf.obj (op U)))) := by sorry
