-- Prove2me | Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul
-- name    : FormalGroup.IsDrinfeldBasisAdic.isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/15bca8c4-cdd2-5102-8772-c10e219b81c9
-- title:
--   Reducedness of the special fibre of a Drinfeld-basis chart
-- statement:
--   Let $q$ be a prime with $q \ge 3$ and let $R$ be a commutative local ring which is Noetherian, adically complete with respect to its maximal ideal, a regular local ring, of Krull dimension $\operatorname{ringKrullDim} R = 2$, with residue field of characteristic $q$ and finite. Let $F$ be a commutative formal group over $R$, and let $x_0, x_1 \in R$ be elements generating the maximal ideal, $\mathfrak m_R = (x_0, x_1)$, such that $F$ satisfies `IsDrinfeldBasisAdic` for the ideal $\mathfrak m_R$, the integer $q$ and the pair $x_0, x_1$: with respect to the $\mathfrak m_R$-adic uniformity on $R$, there is a unit $u$ of $R[[\,\cdot\,]]$ with $F.\mathrm{nthSeries}\ q = u \cdot F.\mathrm{drinfeldDivisor}\ q\ x_0\ x_1$. Let $A$ be a discrete valuation ring (a commutative domain), $\varpi \in A$ a generator of its maximal ideal, and $\varepsilon \in A$ a unit with $\varpi^{q-1} = \varepsilon \cdot q$ in $A$; let $\iota : A \to R$ be a ring homomorphism which is a local homomorphism. Then the quotient ring $R / (\iota \varpi)$ is reduced.
--
--   This is the statement that the fibre of such a Drinfeld-basis chart over the closed point of the base discrete valuation ring has no nilpotents, in the style of the reducedness results for Drinfeld level structures of Katz–Mazur. It is used in the analysis of the adic completion of a modular curve with full level structure, via [`ModularCurve.FullLevel.isReduced_adicCompletion_quotient_span_one_sub_of_isPrimitiveRoot_of_nthSeries_eq_mul_X_pow_mul_levelModuliPackageAbs_gamma0Pow`](thm.html#ModularCurve.FullLevel.isReduced_adicCompletion_quotient_span_one_sub_of_isPrimitiveRoot_of_nthSeries_eq_mul_X_pow_mul_levelModuliPackageAbs_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsDrinfeldBasisAdic_isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem FormalGroup.IsDrinfeldBasisAdic.isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hreg : IsRegularLocalRing R) (hdim : ringKrullDim R = 2)
    (hchar : CharP (ResidueField R) q) [Finite (ResidueField R)]
    (F : FormalGroup R) [F.IsComm]
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)

    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (ε : A) (hε : IsUnit ε) (hϖq : ϖ ^ (q - 1) = ε * (q : A))
    (ι : A →+* R) [IsLocalHom ι] :
    IsReduced (R ⧸ Ideal.span {ι ϖ}) := by sorry
