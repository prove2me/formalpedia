-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_eq_of_comap_toValuationSubring_eq_of_isRational
-- name    : AlgebraicCurve.Place.eq_of_comap_toValuationSubring_eq_of_isRational
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/8abc98a4-1d80-5c79-a2a6-edb8c2650f80
-- title:
--   Uniqueness of places above a rational place
-- statement:
--   Let $K \subseteq K'$ and $F \subseteq F'$ be fields with $F$ an extension of $K$, $F'$ an extension of $K'$, and with the two towers compatible: $K \to K' \to F'$ and $K \to F \to F'$ both commute with the given $K$-algebra structure on $F'$. Assume that $F'$ is generated as a field over $K'$ by the image of $F$, i.e. the intermediate field $K'(\mathrm{im}(F \to F'))$ of $F'/K'$ is all of $F'$. Let $V$ be a place of $F$ over $K$, that is, a valuation subring $\mathcal{O}_V \subseteq F$ containing the image of $K$, different from $F$ itself, and whose underlying ring is a principal ideal ring; assume $V$ is rational, meaning that the structure map from $K$ to the residue field $\mathcal{O}_V/\mathfrak{m}_V$ is surjective. Let $w$ and $w'$ be places of $F'$ over $K'$ (valuation subrings of $F'$ containing $K'$, proper, principal) such that the preimages of $\mathcal{O}_w$ and of $\mathcal{O}_{w'}$ under $F \to F'$ both equal $\mathcal{O}_V$. Then $w = w'$.
--
--   This is the uniqueness half of the classical statement that a rational place of a function field does not split in an extension of the constant field: at most one place of $F'/K'$ restricts to a given rational place of $F/K$ (existence of such a place is a separate assertion). It is used in the construction of the bijection between a class set and the relevant sets of places in the Cerednik–Drinfeld material, and in the analysis of places of modular curves fixed by the square of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_eq_of_comap_toValuationSubring_eq_of_isRational.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

theorem
AlgebraicCurve.Place.eq_of_comap_toValuationSubring_eq_of_isRational
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F'] [Algebra K K']
    [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (V : Place K F) (hV : V.IsRational) (w w' : Place K' F')
    (hw : w.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring)
    (hw' : w'.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring) :
    w = w' := by sorry
