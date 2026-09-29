-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois
-- name    : AlgebraicCurve.Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/5b3cd07a-7875-56e2-85fa-7c8eee61cda1
-- title:
--   Wild lower bound for the different exponent
-- statement:
--   Let $K$ be an algebraically closed field, let $E$ and $M$ be fields with $K$-algebra structures and an $E$-algebra structure on $M$ forming a scalar tower over $K$, and suppose $M$ is finite-dimensional and Galois over $E$. Let $p$ be a prime and suppose $K$ has characteristic $p$. Let $x \in E$, and assume $M$ is finite-dimensional over the intermediate field of $M/K$ generated over $K$ by the single element $\mathrm{alg}_{E \to M}(x)$. Let $P$ be a place of $M$ over $K$, i.e. a valuation subring of $M$ containing the image of $K$, distinct from $M$ itself and a principal ideal ring; write $\operatorname{ord}_P$ for minus the logarithm of the associated height-one adic valuation. Assume that $x$ has order $1$ at the restricted place $P|_E$, the place of $E$ whose valuation subring is the preimage of that of $P$ under $E \to M$. Let $a$ be a natural number with $p^a \mid \operatorname{ord}_P(\mathrm{alg}_{E \to M}(x))$ in $\mathbb{Z}$. Then
--   $$\operatorname{ord}_P(\mathrm{alg}_{E \to M}(x)) - 1 + (p^a - 1) \le \operatorname{ord}_P\bigl(\operatorname{diffCoeff}_{t}(d(\mathrm{alg}_{E \to M}(x)))\bigr),$$
--   where the right-hand side is `ordDiff` of the Kähler differential $d(\mathrm{alg}_{E \to M}(x)) \in \Omega_{M/K}$: a uniformizer $t$ at $P$ (an element of order $1$, chosen by `uniformizer_alt`) is fixed, and $\operatorname{diffCoeff}_t$ returns a coefficient $g \in M$ with $g \cdot dt$ equal to the given differential.
--
--   This is the lower bound contained in Hilbert's different formula for a place of a Galois cover of curves over an algebraically closed field of characteristic $p$: the order of $dx$ at $P$ bounds below by $(e-1)+(p^a-1)$ whenever $p^a$ divides the ramification index $e = \operatorname{ord}_P(x)$, the term $p^a - 1$ recording wild ramification. It is used in the estimates on the order of $dj$ along the modular curve maps, and thence in the bound on the index by a sum of different exponents and double coset counts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve KaehlerDifferential

theorem AlgebraicCurve.Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois
    {K E M : Type*} [Field K] [IsAlgClosed K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional E M] [IsGalois E M]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (x : E) [FiniteDimensional (IntermediateField.adjoin K ({algebraMap E M x} : Set M)) M]
    (P : Place K M) (hx : (P.restrict E).ord x = 1)
    (a : ℕ) (ha : (p : ℤ) ^ a ∣ P.ord (algebraMap E M x)) :
    P.ord (algebraMap E M x) - 1 + ((p : ℤ) ^ a - 1) ≤
      P.ordDiff (D K M (algebraMap E M x)) := by sorry
