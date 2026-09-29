-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing
-- name    : AlgebraicCurve.exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/db18332b-9e06-5ebb-9592-3e818b274bee
-- title:
--   Normal noetherian local subrings of a curve are valuation rings of places
-- statement:
--   Let $L$ be an algebraically closed field and let $F$ be a field equipped with an $L$-algebra structure such that $F$ is a curve over $L$ in the sense of the predicate `IsCurveOver`: the extension $F/L$ has principal divisors (every $f \in F$ with $f \neq 0$ admits a divisor $D$ of degree $0$ with $D(v) = v.\mathrm{ord}(f)$ at every place $v$ of $F/L$), every place $v$ of $F/L$ has residue field finite as an $L$-module, and the module of Kähler differentials $\Omega_{F/L}$ is free of rank $1$ over $F$. Let $R$ be a subring of $F$ which is a local ring, is a noetherian ring, has $F$ as its fraction field, is integrally closed in $F$, contains $\operatorname{image}$ of the structure map $L \to F$ (i.e. $a \in L$ implies the image of $a$ lies in $R$), and is not the whole of $F$. Then there is a place $P$ of $F/L$ — that is, a valuation subring of $F$ containing the image of $L$, different from $F$, and whose underlying ring is a principal ideal ring — whose valuation subring, viewed as a subring of $F$, is exactly $R$.
--
--   This is the standard identification of the local rings of a smooth curve with the valuation rings of its places, in the form used to compare an abstract normal noetherian local subring of a one-variable function field with the points of the associated curve: the hypotheses force $R$ to be a discrete valuation ring with fraction field $F$. It is used in the project's treatment of properness and of integral points on curves, being cited by [`AlgebraicCurve.existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed`](thm.html#AlgebraicCurve.existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed) and by [`AlgebraicCurve.mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed`](thm.html#AlgebraicCurve.mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing
    {L F : Type*} [Field L] [IsAlgClosed L] [Field F] [Algebra L F] [IsCurveOver L F]
    (R : Subring F) [IsLocalRing ↥R] [IsNoetherianRing ↥R] [IsFractionRing ↥R F]
    (hn : IsIntegrallyClosedIn ↥R F)
    (hL : ∀ a : L, algebraMap L F a ∈ R) (hR : R ≠ ⊤) :
    ∃ P : Place L F, P.toValuationSubring.toSubring = R := by sorry
