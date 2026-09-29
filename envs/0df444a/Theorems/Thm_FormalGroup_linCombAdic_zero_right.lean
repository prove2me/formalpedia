-- Prove2me | Theorems.Thm_FormalGroup_linCombAdic_zero_right
-- name    : FormalGroup.linCombAdic_zero_right
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/cf8f4e82-c434-51c4-af72-bdf302a96987
-- title:
--   Adic linear combination with b=0: F([a]x,[0]y)=[a]x
-- statement:
--   Let $T$ be a commutative ring, let $I \subseteq T$ be an ideal for which $T$ is $I$-adically complete, and let $F$ be a one-dimensional formal group law over $T$. Let $x, y \in T$ with $x \in I$, and let $a \in \mathbb{N}$. All evaluations are taken with respect to the $I$-adic uniform structure on $T$ furnished by the ideal $I$. Recall that `F.evalNSMul` is defined recursively by $[0]_F(z) = 0$ and $[n+1]_F(z) = F([n]_F(z), z)$, where $F(u,v)$ denotes the evaluation `F.eval` of the two-variable power series of $F$ at $(u,v)$, and that `F.linCombAdic I x₀ x₁ a b` is $F([a]_F(x_0), [b]_F(x_1))$ computed with this $I$-adic structure. The assertion is that
--   $$F\bigl([a]_F(x), [0]_F(y)\bigr) = [a]_F(x),$$
--   that is, the linear combination `F.linCombAdic I x y a 0` equals `F.evalNSMul a x`. No hypothesis is imposed on $y$, and the second multiplier is literally $0$, so this is the degenerate case of the two-variable linear combination rather than a general unit-axiom statement.
--
--   This is the unit axiom of a formal group law, $F(z,0) = z$, in the $I$-adic evaluated form needed when the two-parameter linear combination $[a]_F(x_0) +_F [b]_F(x_1)$ is specialised at $b = 0$. It serves as normalisation plumbing for the Drinfeld-basis criteria [`WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_nsmul_eq_one_and_nthSeries_eq_mul_prod_of_reducesToOrigin`](thm.html#WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_nsmul_eq_one_and_nthSeries_eq_mul_prod_of_reducesToOrigin) and [`WeierstrassCurve.DrinfeldGlobal.torsionIdeal_le_basisDivisor_of_nsmul_eq_one_of_nthSeries_eq_mul_prod`](thm.html#WeierstrassCurve.DrinfeldGlobal.torsionIdeal_le_basisDivisor_of_nsmul_eq_one_of_nthSeries_eq_mul_prod), where the origin parameter of $[a]P + [0]Q$ must be recognised as $[a]_F(x)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_linCombAdic_zero_right.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem FormalGroup.linCombAdic_zero_right
    {T : Type} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T)
    (x y : T) (hx : x ∈ I) (a : ℕ) :
    F.linCombAdic I x y a 0 = (letI : WithIdeal T := ⟨I⟩; F.evalNSMul a x) := by sorry
