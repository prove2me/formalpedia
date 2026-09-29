-- Prove2me | Theorems.Thm_AlgebraicGeometry_fppfCohomologyMap_one_injective_of_shortExact_of_subsingleton_over
-- name    : AlgebraicGeometry.fppfCohomologyMap_one_injective_of_shortExact_of_subsingleton_over
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/30b28dbd-190f-51b7-b8af-a2c147993db3
-- title:
--   Surjectivity of sections and injectivity on fppf H¹
-- statement:
--   Let $Z_0$ be a scheme, and let $S$ be a short complex $S_1 \xrightarrow{f} S_2 \xrightarrow{g} S_3$ of abelian sheaves on the big fppf site of schemes, assumed short exact. Three hypotheses are imposed. First, for every scheme $Y$ admitting a morphism $Y \to Z_0$, the group $S_1(Y)$ of sections is a subsingleton, i.e. trivial. Second, for every commutative ring $R$ that is flat as a $\mathbf{Z}$-module and every section $s \in S_2(\operatorname{Spec} R)$ such that the restriction of $s$ along $k$ vanishes for every scheme $Y$, every morphism $k : Y \to \operatorname{Spec} R$ and every morphism $Y \to Z_0$, the section $s$ lies in the image of $f$ at $\operatorname{Spec} R$. Third, the restriction map $S_2(\operatorname{Spec}\mathbf{Z}) \to S_2(Z_0)$ along the unique morphism from $Z_0$ to the terminal scheme $\operatorname{Spec}\mathbf{Z}$ is surjective. The conclusion is twofold: the map $g$ on sections over $\operatorname{Spec}\mathbf{Z}$ is surjective, and the map induced by $f$ in degree $1$ is injective, where for a sheaf $F$ the group $F.H\,n$ is the $n$-th Ext group out of the constant sheaf attached to $\mathbf{Z}$ and the induced map is postcomposition with the degree-zero Ext class of $f$.
--
--   This is the cohomological mechanism attached to an extension by zero across a fibre: a subsheaf with no sections over schemes lying over $Z_0$, whose sections over flat $\mathbf{Z}$-algebras are detected by vanishing on such schemes, yields a vanishing connecting homomorphism as soon as sections over $\operatorname{Spec}\mathbf{Z}$ surject onto sections over $Z_0$. It is used in the analysis of fppf cohomology of finite flat group schemes over $\operatorname{Spec}\mathbf{Z}$, via [`ModularCurve.exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two`](thm.html#ModularCurve.exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_fppfCohomologyMap_one_injective_of_shortExact_of_subsingleton_over.lean

import Mathlib.RingTheory.Flat.Basic
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.fppfCohomologyMap_one_injective_of_shortExact_of_subsingleton_over
    (Z₀ : Scheme.{0})
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{0} Ab.{1})} (hS : S.ShortExact)
    (h1 : ∀ Y : Scheme.{0}, (Y ⟶ Z₀) → Subsingleton (S.X₁.obj.obj (op Y)))
    (h2 : ∀ (R : Type) [CommRing R] [Module.Flat ℤ R]
        (s : S.X₂.obj.obj (op (Spec (CommRingCat.of R)))),
      (∀ (Y : Scheme.{0}) (k : Y ⟶ Spec (CommRingCat.of R)), (Y ⟶ Z₀) →
          S.X₂.obj.map k.op s = 0) →
      s ∈ Set.range (S.f.hom.app (op (Spec (CommRingCat.of R)))))
    (h3 : Function.Surjective (S.X₂.obj.map (specZIsTerminal.from Z₀).op)) :
    Function.Surjective (S.g.hom.app (op (Spec (CommRingCat.of ℤ)))) ∧
      Function.Injective (FppfCohomologyLES.cohomologyMap S.f 1) := by sorry
