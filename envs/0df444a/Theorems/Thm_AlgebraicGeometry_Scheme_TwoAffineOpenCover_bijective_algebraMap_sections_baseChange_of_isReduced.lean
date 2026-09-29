-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_algebraMap_sections_baseChange_of_isReduced
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.bijective_algebraMap_sections_baseChange_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/3f29d897-2e1b-5b82-a28c-ccc9eea8de99
-- title:
--   Universal f_*mathcal O_X=𝒪 over a reduced Noetherian base
-- statement:
--   Let $R$ be a Noetherian reduced commutative ring, $X$ a scheme, and $\mathcal V$ a two-chart affine open cover of $X$: a pair of opens $U_0,U_1\subseteq X$, both affine, with $U_0\sqcup U_1=\top$ and $U_0\sqcap U_1$ affine. Let $c\colon X\to\operatorname{Spec}R$ be flat. Associated with $\mathcal V$ and $c$ is the Čech datum of the structure sheaf, with modules $\Gamma(X,U_0)$, $\Gamma(X,U_1)$, $\Gamma(X,U_0\sqcap U_1)$ (each an $R$-algebra through $c$) and differential $d(s_0,s_1)=s_1|_{U_0\sqcap U_1}-s_0|_{U_0\sqcap U_1}$; its $H^0$ is $\ker d$ and its $H^1$ is $\Gamma(X,U_0\sqcap U_1)/\operatorname{im}d$. Assume both are finite $R$-modules, and assume that for every field $K$ equipped with an $R$-algebra structure one has $\dim_K\ker(d\otimes_R K)=1$ (a hypothesis imposed for all $R$-algebra fields, not merely for the residue fields of $R$). Then for every commutative $R$-algebra $A$, writing $\operatorname{Spec}A\to\operatorname{Spec}R$ for the map induced by $R\to A$, the structure morphism $A\to\Gamma(X\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ — the $A$-algebra structure coming from the second projection of the pullback — is bijective.
--
--   This is the statement that $c_*\mathcal O_X=\mathcal O_{\operatorname{Spec}R}$ holds universally, i.e. is preserved by arbitrary (possibly non-reduced) affine base change, for a flat morphism covered by two affine charts whose field-valued fibres satisfy $h^0=1$. It is used for smooth proper curves over a base and, through them, for the global sections of base changes of the Deligne–Rapoport models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_algebraMap_sections_baseChange_of_isReduced.lean

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.bijective_algebraMap_sections_baseChange_of_isReduced
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) [Flat c]
    (hfin : Module.Finite R (𝒱.structureSheafSections c).H0 ∧ Module.Finite R (𝒱.structureSheafSections c).H1)
    (hH0 : ∀ (K : Type u) [Field K] [Algebra R K],
      Module.finrank K (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K)) = 1)
    (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)) := by sorry
