-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_localRing_le_and_exists_mem_localRing_mul_eq_of_specializes
-- name    : AlgebraicCurve.SemistableModel.localRing_le_and_exists_mem_localRing_mul_eq_of_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/a019bcef-a108-5bd6-9e5c-f89e8bb7159a
-- title:
--   Local rings along a specialisation, as subrings of F
-- statement:
--   Let $F$ be a field, let $X$ be a scheme (in the bottom universe) which is integral, and let $\varphi : F \simeq X.\mathrm{functionField}$ be a ring isomorphism of $F$ with the function field of $X$; for a point $y$ of $X$, write $\mathcal O_y$ for the subring `SemistableModel.localRing X φ y` of $F$, that is, the image in $F$ under $\varphi^{-1}$ of the range of the canonical map from the stalk $\mathcal O_{X,y}$ to the function field of $X$. Let $x,\eta$ be points of $X$ with $\eta \rightsquigarrow x$, i.e. $x$ lies in the closure of $\{\eta\}$. The conclusion is a conjunction. First, $\mathcal O_x \le \mathcal O_\eta$ as subrings of $F$. Second, for every $z \in F$ lying in $\mathcal O_\eta$ there exist $f,g \in F$ such that $f \in \mathcal O_x$, $g \in \mathcal O_x$, the element $g$ has a multiplicative inverse inside $\mathcal O_\eta$ (there is $g' \in \mathcal O_\eta$ with $gg' = 1$), and $z g = f$. Thus every element of $\mathcal O_\eta$ is a fraction $f/g$ with $f,g \in \mathcal O_x$ and $g$ invertible in $\mathcal O_\eta$.
--
--   This records, in the currency of subrings of $F$ used throughout the semistable-model formalism, the standard fact that for a generisation $\eta$ of $x$ the stalk $\mathcal O_{X,\eta}$ is a localisation of $\mathcal O_{X,x}$. It is used in the analysis of local rings and residue maps on semistable models, for instance in the study of node coordinates and branches and in the construction of semistable schemes over the descent base for full-level modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_localRing_le_and_exists_mem_localRing_mul_eq_of_specializes.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicGeometry CategoryTheory

theorem AlgebraicCurve.SemistableModel.localRing_le_and_exists_mem_localRing_mul_eq_of_specializes
    {F : Type} [Field F] (X : Scheme.{0}) [IsIntegral X] (φ : F ≃+* X.functionField)
    {x η : X} (h : η ⤳ x) :
    SemistableModel.localRing X φ x ≤ SemistableModel.localRing X φ η ∧
    ∀ z : F, z ∈ SemistableModel.localRing X φ η →
      ∃ f g : F, f ∈ SemistableModel.localRing X φ x ∧ g ∈ SemistableModel.localRing X φ x ∧
        (∃ g' ∈ SemistableModel.localRing X φ η, g * g' = 1) ∧ z * g = f := by sorry
