-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension
-- name    : AlgebraicCurve.exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/4893c972-e348-5943-97ae-7823a940be34
-- title:
--   Regular differentials descend along a constant-field extension
-- statement:
--   Let $K, F, K', F'$ be fields with $F$ a $K$-algebra, $F'$ a $K'$-algebra, together with $K$-algebra maps $K \to K'$, $F \to F'$, $K \to F'$ making $K \to K' \to F'$ and $K \to F \to F'$ scalar towers and with the actions of $K'$ and $F$ on $F'$ commuting; assume $K$ has characteristic $0$, $K'$ is algebraic over $K$ and algebraically closed, and $F'$ is integral over $F$. Assume further: there is $x \in F$ transcendental over $K$ with $F$ finite over $K(x)$, and likewise some $x' \in F'$ transcendental over $K'$ with $F'$ finite over $K'(x')$; `IsCurveOver K' F'` holds, i.e. every nonzero $f \in F'$ has a divisor of degree $0$ whose value at each place is the order of $f$ there, every place of $F'/K'$ has residue field finite over $K'$, and $\Omega_{F'/K'}$ is free of rank $1$ over $F'$; $F'$ is generated as an $F$-algebra by the image of $K'$; and $K$ is algebraically closed in $F$, i.e. every $y \in F$ algebraic over $K$ lies in the image of $K$. Let $\omega \in \Omega_{F/K}$ be such that its image in $\Omega_{F'/K'}$ is a regular differential: for every place $w$ of $F'/K'$ it equals $f \cdot \mathrm{d}(\text{uniformiser of } w)$ for some $f$ in the valuation ring of $w$. Then for every place $v$ of $F/K$ — a valuation subring $\mathcal{O}_v \subsetneq F$ containing the image of $K$ and a principal ideal ring — there exist $c, t \in \mathcal{O}_v$ with $\omega = c \cdot \mathrm{d}t$. The conclusion is shaped slightly differently from membership in `regularDifferentials K F`, in that $t$ is only required to lie in $\mathcal{O}_v$ rather than to be a uniformiser at $v$.
--
--   This is the descent statement that a differential regular at all places of a constant-field extension $F' = K'\cdot F$ is regular at all places of $F/K$, the constant-field extension being unramified. It is used in the analysis of $q$-expansions of cusp forms, where integrality of the $q$-expansion is transferred to a regularity statement for the associated differential on the modular curve over the smaller field of constants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open KaehlerDifferential

theorem AlgebraicCurve.exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
    [CharZero K] [Algebra.IsAlgebraic K K'] [IsAlgClosed K'] [Algebra.IsIntegral F F']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [AlgebraicCurve.IsCurveOver K' F']
    (hfg' : ∃ x : F', Transcendental K' x ∧ FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (ω : Ω[F⁄K]) (hω : KaehlerDifferential.map K K' F F' ω ∈ AlgebraicCurve.regularDifferentials K' F')
    (v : AlgebraicCurve.Place K F) :
    ∃ c ∈ v.toValuationSubring, ∃ t ∈ v.toValuationSubring, ω = c • KaehlerDifferential.D K F t := by sorry
