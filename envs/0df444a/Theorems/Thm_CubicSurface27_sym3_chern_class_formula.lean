-- Prove2me | Theorems.Thm_CubicSurface27_sym3_chern_class_formula
-- name    : CubicSurface27.sym3_chern_class_formula
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T13:52:34.217176+00:00
-- url     : https://prove2.me/theorems/52f4ab0b-6123-4115-9e87-ecdb24725757
-- title:
--   Chern classes of $\mathrm{Sym}^3 E$: $c_4 = 9c_2(2c_1^2 + c_2)$
-- statement:
--   The source's Example computes the Chern classes of $F=\mathrm{Sym}^3E$ for a rank-$2$ bundle $E$ via the splitting principle. Writing $E=L\oplus M$ with Chern roots $\alpha=c_1(L)$, $\beta=c_1(M)$, so $c_1(E)=\alpha+\beta$ and $c_2(E)=\alpha\beta$, the bundle $\mathrm{Sym}^3E$ splits as $L^{\otimes3}\oplus(L^{\otimes2}\otimes M)\oplus(L\otimes M^{\otimes2})\oplus M^{\otimes3}$ with total Chern class $(1+3\alpha)(1+2\alpha+\beta)(1+\alpha+2\beta)(1+3\beta)$.
--
--   The degree-$1$ part gives $c_1(\mathrm{Sym}^3E)=6c_1(E)$; the degree-$4$ part gives
--   $$c_4(\mathrm{Sym}^3E)=9(2\alpha^3\beta+5\alpha^2\beta^2+2\alpha\beta^3)=9c_2(E)\bigl(2c_1(E)^2+c_2(E)\bigr).$$
--   This item states the two universal polynomial identities in the Chern roots $\alpha,\beta$, over any commutative ring.
--
--   **Formalization Note.** The splitting principle is background; the item is the resulting identity, valid for all $\alpha,\beta$ in any commutative ring. The first conjunct is the $c_1$ computation, the second the $c_4$ computation.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora. Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part II, 'Chern classes', the Example computing c₁(F) = 6c₁(E) and c₄(F) = 9c₂(E)(2c₁(E)² + c₂(E)) for F = Sym³E via the splitting principle.

import Mathlib

namespace CubicSurface27

theorem sym3_chern_class_formula {R : Type*} [CommRing R] (α β : R) :
    3 * α + (2 * α + β) + (α + 2 * β) + 3 * β = 6 * (α + β) ∧
    9 * (α * β) * (2 * (α + β) ^ 2 + α * β) =
      9 * (2 * α ^ 3 * β + 5 * α ^ 2 * β ^ 2 + 2 * α * β ^ 3) := by sorry

end CubicSurface27
