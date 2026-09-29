-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_perfectField
-- name    : AlgebraicCurve.exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/17030a11-0380-5281-9bd9-c8683ee51c79
-- title:
--   Separating generation passes to constant field extensions over a perfect field
-- statement:
--   Let $K$, $F$, $K'$, $F'$ be fields with $F$ a $K$-algebra, $F'$ a $K'$-algebra, $K'$ a $K$-algebra, $F'$ an $F$-algebra and an $K$-algebra, the algebra maps being compatible in the sense that $K \to K' \to F'$ and $K \to F \to F'$ are both scalar towers, and suppose $K$ is perfect. Assume: (i) there is $x \in F$ transcendental over $K$ such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`; (ii) there is $x \in F'$ transcendental over $K'$ such that $F'$ is finite-dimensional over $K'(x)$; and (iii) $F'$ is generated over $K'$ by the image of $F$, i.e. the intermediate field of $F'$ generated over $K'$ by the range of the algebra map $F \to F'$ is the whole of $F'$. Then there exists $t' \in F'$ such that $F'$ is finite-dimensional over $K'(t')$ and $F'$ is separable over $K'(t')$. (Note that transcendence of $t'$ over $K'$ is not part of the conclusion, and hypothesis (ii) is used only through the ambient assumptions of the statement.)
--
--   This is the statement that a one-variable function field stays separably generated under an arbitrary constant field extension, provided the base field is perfect: a separating transcendental element $t$ of $F/K$ remains separating for $F' = K'F$ over $K'$. It is used in the treatment of places of constant field extensions, in particular by [`AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic`](thm.html#AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_perfectField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_perfectField
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [PerfectField K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    ∃ t' : F', FiniteDimensional (IntermediateField.adjoin K' ({t'} : Set F')) F' ∧
      Algebra.IsSeparable (IntermediateField.adjoin K' ({t'} : Set F')) F' := by sorry
