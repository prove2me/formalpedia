-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_eq_ord_of_addHom_of_nonneg_iff
-- name    : AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/4848ccd2-4f3f-5109-9c4b-f2a878ae8ccb
-- title:
--   Uniqueness of the order function of a place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $w$ be a place of $F$ over $K$, that is, a valuation subring $\mathcal O_w \subseteq F$ containing $\operatorname{im}(K \to F)$, different from $F$ itself, and whose ring structure is a principal ideal ring; write $\operatorname{ord}_w(f) = -\log\bigl(w_{\mathrm{adic}}(f)\bigr)$ for the integer obtained from the $\mathbb Z^{\mathrm{m}0}$-valued adic valuation attached to the height-one prime of $\mathcal O_w$. Let $\varphi : F \to \mathbb Z$ be any function such that (i) $\varphi(xy) = \varphi(x) + \varphi(y)$ whenever $x \neq 0$ and $y \neq 0$; (ii) there exists $t \neq 0$ with $\varphi(t) = 1$; and (iii) for every $x \neq 0$ one has $0 \le \varphi(x)$ if and only if $x \in \mathcal O_w$. Then for every $x \neq 0$ one has $\varphi(x) = \operatorname{ord}_w(x)$. No condition is imposed on the value $\varphi(0)$, and the conclusion is asserted only at nonzero arguments.
--
--   This is the uniqueness of the normalised discrete valuation attached to a place: a concretely given $\mathbb Z$-valued additive function whose nonnegativity locus is exactly the valuation subring of $w$, and which attains the value $1$, must coincide with the intrinsic order function $\operatorname{ord}_w$ on $F^\times$. It is used to identify $\operatorname{ord}_w$ with an adic valuation computed elsewhere, as in the identification of $\operatorname{ord}_w$ with the valuation at the centre of $w$ in an integral closure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_eq_ord_of_addHom_of_nonneg_iff.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (φ : F → ℤ) (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y) (hone : ∃ t, t ≠ 0 ∧ φ t = 1) (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring)) {x : F} (hx : x ≠ 0) : φ x = w.ord x := by sorry
