-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_one_toBase_ratLocalizedAt_of_forall_pullback_snd
-- name    : AlgebraicCurve.TwoChartIntegralModel.smoothOfRelativeDimension_one_toBase_ratLocalizedAt_of_forall_pullback_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/32f89801-5280-541d-8068-eba15c77d335
-- title:
--   Fibrewise smoothness criterion for a two-chart integral model
-- statement:
--   Fix a natural number $p$ that is prime, and write $R=\mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$. Let $F$ be a field (in `Type`) equipped with an $R$-algebra structure and let $j\in F$ be non-zero (carried by a `Fact` instance). Let $X=\mathrm{TwoChartIntegralModel}\,R\,F\,j$ be the scheme obtained as the pushout of the two morphisms `fFin` and `fInf` from the middle chart to the spectra of the $R$-subalgebras `chartAlgFin` $=$ `chartAlg R F {j}` and `chartAlgInf` $=$ `chartAlg R F {j⁻¹}` of $F$, and let $f=$ `TwoChartIntegralModel.toBase R F j` $:X\to\operatorname{Spec} R$ be the morphism descended from the structure morphisms of the two charts over $R$. Assume $f$ is flat and locally of finite presentation. Assume further that for every field $k$ in `Type` which is algebraically closed and every ring homomorphism $\varphi\colon R\to k$, the second projection $X\times_{\operatorname{Spec} R}\operatorname{Spec} k\to\operatorname{Spec} k$ of the pullback of $f$ along $\operatorname{Spec}\varphi$ is smooth of relative dimension $1$. Then $f$ itself is smooth of relative dimension $1$.
--
--   This is the fibrewise criterion for smoothness of a flat morphism locally of finite presentation, specialised to the two-chart integral model over $\mathbb{Z}_{(p)}$: smoothness of relative dimension one of all geometric fibres implies smoothness of relative dimension one of the structure morphism. It is used in establishing that the two-chart integral model attached to the $q$-expansion of the $j$-invariant is proper, smooth and geometrically integral over $\mathbb{Z}_{(p)}$ for $p$ not dividing the relevant level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_one_toBase_ratLocalizedAt_of_forall_pullback_snd.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.smoothOfRelativeDimension_one_toBase_ratLocalizedAt_of_forall_pullback_snd
    (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ↥(GaloisRep.ratLocalizedAt p) F] (j : F) [Fact (j ≠ 0)]
    [Flat (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j)]
    [LocallyOfFinitePresentation (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j)]
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : ↥(GaloisRep.ratLocalizedAt p) →+* k),
      SmoothOfRelativeDimension 1
        (pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j) (Spec.map (CommRingCat.ofHom φ)))) :
    SmoothOfRelativeDimension 1 (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j) := by sorry
