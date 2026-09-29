-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_canonicalLocalResidueDataK_eq
-- name    : AlgebraicCurve.Place.canonicalLocalResidueDataK_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/55f98691-3e3e-5d56-8d2d-960f464d8e75
-- title:
--   Uniqueness of canonical local residue data at a rational place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, that is, a valuation subring $\mathcal{O}_v \subseteq F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring. Assume $v$ is rational, meaning that the structure map from $K$ to the residue field $\kappa(v) = \mathcal{O}_v/\mathfrak{m}_v$ is surjective. Write $\pi$ for the chosen irreducible element (`uniformizer`) of $\mathcal{O}_v$. A canonical local residue datum over $K$ at $v$ consists of a $K$-linear map $\operatorname{res} \colon F \to \kappa(v)$ such that $\operatorname{res}$ vanishes on every element of $\mathcal{O}_v$; for every $f \in F$ with $\pi f \in \mathcal{O}_v$ one has $\operatorname{res}(f) = \overline{\pi f}$, the residue class of $\pi f$; and $\operatorname{res}\bigl((\pi^{n+1})^{-1}\bigr) = 0$ for every integer $n \ge 1$. The theorem asserts that any two such data $d_1$, $d_2$ at $v$ are equal; equivalently, the type of canonical local residue data over $K$ at a rational place is a subsingleton.
--
--   This is the uniqueness half of the construction of the local residue map at a degree-one (rational) place of a function field: the three axioms — vanishing on the valuation ring, the simple-pole formula, and the vanishing on the higher pole monomials $\pi^{-(n+1)}$, $n \ge 1$ — pin the residue down completely. It is used when residues of differentials on a modular curve are computed term by term, in particular in the evaluation of sums of residue terms attached to Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_canonicalLocalResidueDataK_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.canonicalLocalResidueDataK_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) (d₁ d₂ : v.CanonicalLocalResidueDataK) :
    d₁ = d₂ := by sorry
