-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules
-- name    : AlgebraicGeometry.OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/451c5dc7-a95d-5d52-91bf-187ca4cc4224
-- title:
--   A finite free two-term model for H⁰ under base change
-- statement:
--   Let $R$ be a Noetherian commutative ring, $X$ a scheme and $f\colon X\to\operatorname{Spec}R$ a proper flat morphism. Let $M$ be a sheaf of $\mathcal O_X$-modules, assumed Zariski-locally trivial in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $\mathcal U$ be an ordered affine cover of $X$: a finite linearly ordered index type together with affine opens $U_i$ whose supremum is $\top$. Write $F=$ `OModulePresheaf.ofModules f M` for the presheaf of $R$-modules $U\mapsto\Gamma(M,U)$, the $R$-action coming from $f$ through $\Gamma(X,U)$, with restrictions the restriction maps of $M$; its degree-$i$ cochain module is $\prod_{s\in\mathcal U.\mathrm{Idx}\,i}\Gamma(M,\bigsqcap_j U_{s(j)})$ and its differentials are $F.d$. The assertion is the existence of a two-term complex $G$ of finite free $R$-modules, i.e. $d_G\colon G^0\to G^1$ with $G^0,G^1$ finite and free, of $R$-linear maps $\iota_0\colon G^0\to F.\mathrm{cochain}\,\mathcal U\,0$ and $\iota_1\colon G^1\to F.\mathrm{cochain}\,\mathcal U\,1$, and of a proof that $d^0\circ\iota_0=\iota_1\circ d_G$, such that for every commutative $R$-algebra $A$ in the same universe the induced map $\ker(d_G\otimes_R A)\to\ker(d^0\otimes_R A)$ obtained by restricting $\iota_0\otimes_R A$ is bijective.
--
--   This is the degree-zero part of the base-change theorem for the cohomology of a flat sheaf on a proper scheme (Mumford, Abelian Varieties §5; Hartshorne III.12.2–12.3), in ordered Čech form: global sections after any base change are computed by one fixed two-term complex of finite free $R$-modules. It underlies the later statements about projectivity of $H^0$, the comparison of sections with their base changes, and the closedness of the loci where the rank of the space of sections jumps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
      (ι0 : G.C0 →ₗ[R] (OModulePresheaf.ofModules f M).cochain 𝒰 0)
      (ι1 : G.C1 →ₗ[R] (OModulePresheaf.ofModules f M).cochain 𝒰 1)
      (comm : (OModulePresheaf.ofModules f M).d 𝒰 0 ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective
          (TwoChartCech.kerMapBaseChange G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm A) := by sorry
