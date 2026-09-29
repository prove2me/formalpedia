-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_torsionPoints_eq_pow_four
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.natCard_torsionPoints_eq_pow_four
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/f54acaf6-e305-5645-8ed5-eafe9411a765
-- title:
--   ℓ-torsion of a fake elliptic curve has order ℓ⁴
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $L$ be an algebraically closed field of characteristic $0$ and let $E$ be a term of the structure `FakeEllipticCurve Λ N L`: thus $E$ provides a scheme $E.A$ with a morphism $E.f : E.A \to \operatorname{Spec} L$, a relative group law $E.L$ on $E.f$ (a functorial group structure, with multiplication, unit and inverse compatible with base change, on the sets $\{\varphi : T \to E.A \mid \varphi \text{ followed by } E.f = t\}$ of sections over arbitrary $t : T \to \operatorname{Spec} L$), the commutativity of that law, the property bundle asserting that $E.f$ is smooth and proper with connected fibres, the condition that every fibre of $E.f$ has topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms of $E.A$ over $\operatorname{Spec} L$ which is additive and multiplicative and satisfies a trace condition, together with the curve and level-$N$ data of that structure. Let $\ell$ be a prime. The conclusion is that the set of sections $P$ over the identity of $\operatorname{Spec} L$, that is of $L$-points of $E.A$, satisfying $\ell \cdot P = 1$, where $\ell \cdot P$ is formed by iterating the group law $\ell$ times starting from the unit, has exactly $\ell^4$ elements.
--
--   This is the statement that the $\ell$-torsion of an abelian surface over an algebraically closed field of characteristic $0$ is of order $\ell^4$, specialised to the fake elliptic curves (quaternionic abelian surfaces) used in the Čerednik–Drinfeld description of Shimura curves. It supplies the cardinality input for the analysis of the $\Lambda$-stable subgroups of order $\ell^2$, and is cited in the treatment of extra level structures and in the Eichler–Shimura type computation on the Shimura curve model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_torsionPoints_eq_pow_four.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.natCard_torsionPoints_eq_pow_four
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (L : Type u) [Field L] [IsAlgClosed L] [CharZero L]
    (E : FakeEllipticCurve Λ N L) (ℓ : ℕ) [Fact ℓ.Prime] :
    Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) E.f //
        nsmulPt E.L (𝟙 (Spec (CommRingCat.of L))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of L)))} = ℓ ^ 4 := by sorry
