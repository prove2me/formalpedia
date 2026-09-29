-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_projective_H0_and_bijective_kerBaseChangeHom_of_isReduced_of_finrank_eq
-- name    : AlgebraicGeometry.OModulePresheaf.projective_H0_and_bijective_kerBaseChangeHom_of_isReduced_of_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/a71f97b3-ee55-578e-abb1-0fc804a4af7e
-- title:
--   Čech H⁰ projective and commuting with base change
-- statement:
--   Let $R$ be a reduced Noetherian commutative ring, $X$ a scheme, and $f\colon X\to\operatorname{Spec}R$ a proper flat morphism. Let $M$ be a sheaf of $\mathcal O_X$-modules which is locally trivial in the sense that every point of $X$ has an open neighbourhood $U$ with the pullback of $M$ to $U$ isomorphic to the unit sheaf of modules on $U$, i.e. to $\mathcal O_U$. Let $r$ be a natural number and assume that for every prime $\mathfrak p$ of $R$, the global sections over $\top$ of the pullback of $M$ along the first projection of the fibre product of $f$ with $\operatorname{Spec}\kappa(\mathfrak p)\to\operatorname{Spec}R$, taken as a module over $\kappa(\mathfrak p)$ via the second projection, has finrank equal to $r$. Let $\mathcal U$ be an ordered affine cover of $X$: a finite, linearly ordered family of affine opens $U_i$ with $\bigsqcup_i U_i=\top$. Consider the presheaf of $R$-modules $U\mapsto \Gamma(M,U)$, the $R$-action coming from $R\to\Gamma(X,U)$ induced by $f$, and its degree $0$ Čech differential $d^0$ on $\mathcal U$. Then the $R$-module $H^0=\ker d^0$ is projective, and for every commutative $R$-algebra $A$ the canonical map $A\otimes_R\ker d^0\to\ker(d^0\otimes_R A)$ induced by the inclusion of $\ker d^0$ is bijective. Finite generation of $H^0$, and that its rank equals $r$, are not asserted.
--
--   This is cohomology and base change in degree $0$ over a reduced base with constant fibrewise $h^0$, in the alternating Čech formulation for a proper flat family and a locally trivial (invertible) sheaf: constancy of $h^0$ forces $f_*M$ to be flat and its formation to commute with arbitrary base change. It is used to produce, over a reduced base, a global section generating $M$ fibrewise, in the form cited by [`AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_projective_H0_and_bijective_kerBaseChangeHom_of_isReduced_of_finrank_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.projective_H0_and_bijective_kerBaseChangeHom_of_isReduced_of_finrank_eq
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (r : ℕ)
    (hconst : ∀ 𝔭 : PrimeSpectrum R,
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤) = r)
    (𝒰 : X.OrderedAffineCover) :
    Module.Projective R ((OModulePresheaf.ofModules f M).H0 𝒰) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom ((OModulePresheaf.ofModules f M).d 𝒰 0) A) := by sorry
