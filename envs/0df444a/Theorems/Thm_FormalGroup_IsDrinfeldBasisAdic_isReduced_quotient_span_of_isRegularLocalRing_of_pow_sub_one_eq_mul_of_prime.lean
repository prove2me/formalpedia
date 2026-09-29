-- Prove2me | Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul_of_prime
-- name    : FormalGroup.IsDrinfeldBasisAdic.isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/d87cda48-639b-5654-9f9f-c043fdd50ce5
-- title:
--   Reducedness of the special fibre of a Drinfeld-basis chart
-- statement:
--   Fix a prime $q$ and let $R$ be a Noetherian local ring, complete with respect to its maximal ideal $\mathfrak m_R$, which is a regular local ring of Krull dimension $2$ and whose residue field is finite of characteristic $q$. Let $F$ be a commutative formal group law over $R$, and let $x_0, x_1 \in R$ be elements generating $\mathfrak m_R$, i.e. $\mathfrak m_R = (x_0, x_1)$, which satisfy the hypothesis `F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁`: giving $R$ its $\mathfrak m_R$-adic uniform structure, there is a unit power series $u$ over $R$ with $F.\mathrm{nthSeries}\,q = u \cdot F.\mathrm{drinfeldDivisor}\,q\,x_0\,x_1$, so that the $q$-division series of $F$ differs from the Drinfeld divisor attached to $q, x_0, x_1$ by a unit. Let furthermore $A$ be a discrete valuation ring (a domain) with $\mathfrak m_A = (\varpi)$, let $\varepsilon \in A$ be a unit with $\varpi^{\,q-1} = \varepsilon \, q$ in $A$, and let $\iota : A \to R$ be a local ring homomorphism. The conclusion is that the quotient $R/(\iota\varpi)$ is a reduced ring.
--
--   This is the statement that the fibre over the closed point of $A$ of a Drinfeld-basis chart — in the classical setting, the completed local ring of a modular curve with full level-$q$ structure at a supersingular point, with $A$ a ramified base such as $\mathbb Z_q[\varpi]/(\varpi^{q-1} - \varepsilon q)$ — has reduced special fibre, in the style of the reducedness results of Katz–Mazur for $\Gamma(q)$-moduli. It is used in the analysis of the full-level modular curve, in the reducedness statement for the adic completion at a point where the $q$-division series factorises through a power of $X$ times the rigid local datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsDrinfeldBasisAdic_isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul_of_prime.lean

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

theorem FormalGroup.IsDrinfeldBasisAdic.isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul_of_prime
    (q : ℕ) [Fact q.Prime]
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
