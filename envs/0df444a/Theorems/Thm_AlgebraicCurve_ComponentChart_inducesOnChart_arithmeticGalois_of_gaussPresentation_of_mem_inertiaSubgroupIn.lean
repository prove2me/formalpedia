-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_inducesOnChart_arithmeticGalois_of_gaussPresentation_of_mem_inertiaSubgroupIn
-- name    : AlgebraicCurve.ComponentChart.inducesOnChart_arithmeticGalois_of_gaussPresentation_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/40021061-af99-58d3-9f62-1067fdacc91d
-- title:
--   Inertia induces the identity on a Gauss-presented component chart
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number, let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and let `Fbar` be a field equipped with an algebra structure over the residue field of $A$. Let $C$ be a `ComponentChart A (fieldBar q M') Fbar`, that is, a valuation subring `C.integers` of the field $F =$ `fieldBar q M'` $=$ `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')` (the base change to $\overline{\mathbb{Q}}$, inside $\overline{\mathbb{Q}}((q))$, of the function field of $X_H$ at level $q^2M'$ with $H$ the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$), together with a surjective residue map `C.residue` onto `Fbar` with kernel the maximal ideal, a set of places, a finite set of nodes and a map on places, subject to the compatibility axioms of that structure. Assume `C.integers` admits the Gauss presentation: for $f \in F$, $f \in$ `C.integers` if and only if there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ to the residue field of $A$ is nonzero and $f \cdot y = x$ in $\overline{\mathbb{Q}}((q))$, the coefficients of $x$, $y$ being mapped in along $A \hookrightarrow \overline{\mathbb{Q}}$. Let $\tau$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ lying in `A.inertiaSubgroupIn ℚ`, the image in the full automorphism group of the inertia subgroup of the decomposition subgroup of $A$. Then the $\tau$-semilinear automorphism [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54) of $F$, acting coefficientwise on $q$-expansions, induces on the chart $C$ the identity ring automorphism of `Fbar`: for every $f \in F$ one has $f \in$ `C.integers` if and only if $\tau \cdot f \in$ `C.integers`, and for every $f \in$ `C.integers` the residue of $\tau \cdot f$ equals the residue of $f$.
--
--   This is the statement that inertia at $A$ acts trivially on the reduction of a component of the modular curve whose chart is cut out by the Gauss valuation on $q$-expansions; no tameness assumption on $\tau$ enters. It supplies the inertia clause for the Igusa components in the construction of the full-level semistable covering, and is cited by [`ModularCurve.FullLevel.SemistableCovering.inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap`](thm.html#ModularCurve.FullLevel.SemistableCovering.inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap) and by the existence theorems for that covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_inducesOnChart_arithmeticGalois_of_gaussPresentation_of_mem_inertiaSubgroupIn.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel AlgebraicCurve IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem AlgebraicCurve.ComponentChart.inducesOnChart_arithmeticGalois_of_gaussPresentation_of_mem_inertiaSubgroupIn
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A (fieldBar q M') Fbar)
    (hO : ∀ f : fieldBar q M', f ∈ C.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ) :
    SemistableCovering.InducesOnChart C
      (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) (RingEquiv.refl _) := by sorry
