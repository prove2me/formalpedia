-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound
-- name    : AlgebraicCurve.Place.exists_ord_mul_eq_order_of_hasRamBound
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/843b7273-d68e-53c8-8f36-cdb31c8739f3
-- title:
--   Hahn-series embedding with bounded ramification yields a place
-- statement:
--   Let $K$, $L$, $F$ be fields with $L$ and $F$ both $K$-algebras, and let $\varphi \colon F \to \mathrm{HahnSeries}\,\mathbb{Q}\,L$ be a homomorphism of $K$-algebras into the field of Hahn series with rational exponents and coefficients in $L$. Let $d$ be a natural number with $0 < d$, and assume the ramification of $\varphi$ is bounded by $d$ in the sense that for every $x \in F$ the support of $\varphi(x)$ is contained in $\{k/d : k \in \mathbb{Z}\} \subseteq \mathbb{Q}$. Assume further that $\varphi$ is nontrivial for the order function, i.e. there is some $x \in F$ with $\mathrm{order}(\varphi(x)) \neq 0$. The conclusion asserts the existence of a place $w$ of $F$ over $K$ — that is, a valuation subring of $F$ containing the image of $K$ under the structure map, different from $F$ itself, and whose underlying ring is a principal ideal ring — together with a rational number $g > 0$ such that for all $x \in F$ one has $(\mathrm{ord}_w x) \cdot g = \mathrm{order}(\varphi(x))$, where $\mathrm{ord}_w x \in \mathbb{Z}$ is the negative of the logarithm of the adic valuation attached to the height-one prime of $w$, viewed in $\mathbb{Q}$.
--
--   This is the statement that the $t$-adic order pulled back along an embedding of $F$ into Hahn series with exponents in $\frac1d\mathbb{Z}$ is, up to a positive rational scaling factor $g$ generating its value group, the normalised valuation of a place of $F$ over $K$. It is the basic tool used to produce places from Puiseux- or Laurent-series expansions, and is invoked by the corresponding statement for embeddings into Laurent series and by the divisibility and ramification-index computations for such embeddings in the Galois case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.exists_ord_mul_eq_order_of_hasRamBound
    {K L F : Type*} [Field K] [Field L] [Algebra K L] [Field F] [Algebra K F]
    (φ : F →ₐ[K] HahnSeries ℚ L) {d : ℕ} (hd : 0 < d)
    (hφ : ∀ x : F, HahnSeries.HasRamBound d (φ x))
    (hnt : ∃ x : F, (φ x).order ≠ 0) :
    ∃ (w : AlgebraicCurve.Place K F) (g : ℚ), 0 < g ∧
      ∀ x : F, (w.ord x : ℚ) * g = (φ x).order := by sorry
