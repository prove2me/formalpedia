-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes
-- name    : AlgebraicCurve.TwoChartIntegralModel.ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/60260efd-3753-597d-beed-0308c0f4c945
-- title:
--   Dimension two at a crossing of the two-chart integral model
-- statement:
--   Let $R$ be a Noetherian domain whose Krull dimension `ringKrullDim R` equals $1$, let $F$ be a field equipped with an $R$-algebra structure for which $\mathrm{algebraMap}\,R\,F$ is injective, and let $j \in F$ be non-zero. Write $X =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) for the scheme obtained as the pushout of the two morphisms `fFin` and `fInf`, namely the maps of spectra induced by the inclusions `inclFin` and `inclInf` of the $R$-subalgebras `chartAlg R F {j}` and `chartAlg R F {j⁻¹}` of $F$ into the common algebra indexing `XMid`, and let `toBase` $: X \to \operatorname{Spec} R$ be the morphism determined by the structure maps of these two subalgebras. Let $\varpi \in R$, let $z$ be a point of $X$, and let $\varpi_z$ be an element of the stalk $\mathcal{O}_{X,z}$ which is assumed to be the germ at $z$ of the global section of $X$ obtained by pulling back $\varpi$ along `toBase` (via the canonical identification of $R$ with the global sections of $\operatorname{Spec} R$). Assume the set of minimal primes of the ideal $(\varpi_z) \subseteq \mathcal{O}_{X,z}$ is not a subsingleton, i.e. it contains at least two distinct members. Then `ringKrullDim` of $\mathcal{O}_{X,z}$ equals $2$.
--
--   This is the dimension input at a point where at least two branches of the fibre $\varpi = 0$ meet: the existence of two distinct minimal primes over $\varpi_z$ in the local ring of the two-chart integral model forces that local ring to have dimension exactly $2$, the proof using that $X$ is an integral scheme ([`AlgebraicCurve.TwoChartIntegralModel.isIntegral`](thm.html#AlgebraicCurve.TwoChartIntegralModel.isIntegral)). It is used in the analysis of the two-chart model attached to $X_1$-type modular curves, supplying the hypothesis $\dim \mathcal{O}_{X,z} = 2$ of the regularity criterion at the crossing points of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicCurve.TwoChartIntegralModel.ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (hR : ringKrullDim R = 1)
    (F : Type u) [Field F] [Algebra R F] (hinj : Function.Injective (algebraMap R F))
    (j : F) [Fact (j ≠ 0)]
    (ϖ : R) (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)))
    (hmany : ¬ ((Ideal.span {ϖz} : Ideal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)).minimalPrimes).Subsingleton) :
    ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) = 2 := by sorry
