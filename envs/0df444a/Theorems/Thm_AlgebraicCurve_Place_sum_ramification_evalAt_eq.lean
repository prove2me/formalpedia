-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_sum_ramification_evalAt_eq
-- name    : AlgebraicCurve.Place.sum_ramification_evalAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/6ae5e3de-0253-570a-961c-79d9be989098
-- title:
--   Riemann–Hurwitz formula in terms of the values of x
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure which is a curve over $\mathbb{C}$, i.e. every nonzero $f \in F$ has a finitely supported divisor recording the orders $v.\mathrm{ord}\, f = -\log v(f)$ at all places and of degree $0$, every place has residue field finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$; here a place is a valuation subring of $F$, not all of $F$, containing the image of $\mathbb{C}$ and a principal ideal ring. Assume also that every nonzero $\omega \in \Omega[F/\mathbb{C}]$ admits a finitely supported divisor whose value at each place $v$ is $v.\mathrm{ord}$ of the coefficient of $\omega$ against $d$ of a uniformizer at $v$. Let $x \in F$ be transcendental over $\mathbb{C}$ with $F$ finite-dimensional over $\mathbb{C}(x) = \mathbb{C}\text{-adjoin}\,\{x\}$. Let $B \subseteq \mathbb{C}$ be a finite set containing every $b$ that is the value $\mathrm{evalAt}_w(x)$ (the residue of $x$, transported to $\mathbb{C}$ by a left inverse of $\mathbb{C} \to$ residue field) at some place $w$ with $x$ in the valuation subring of $w$ and with $(\mathrm{ord}_w(x - b))^{+} \neq 1$, where $(\cdot)^{+}$ denotes truncation to $\mathbb{N}$. Let $t : \mathbb{C} \to$ finite sets of places satisfy, for $b \in B$: $w \in t(b)$ iff $x$ lies in the valuation subring of $w$ and $\mathrm{evalAt}_w(x) = b$; and let $p$ be the finite set of places $w$ with $x \notin w$'s valuation subring. Then $$\sum_{b \in B} \sum_{w \in t(b)} \big((\mathrm{ord}_w(x-b))^{+} - 1\big) + \sum_{w \in p} \big((\mathrm{ord}_w(x^{-1}))^{+} - 1\big) = 2\dim_{\mathbb{C}} \Omega_{\mathrm{reg}} - 2 + 2\,[F : \mathbb{C}(x)],$$ where $\Omega_{\mathrm{reg}}$ is the space of differentials $\omega$ such that at each place $w$ one has $\omega = f \cdot d(\text{uniformizer at } w)$ with $f$ in the valuation subring of $w$.
--
--   This is the Riemann–Hurwitz (Hurwitz genus) formula for the map given by $x$, written in terms of the finite values of $x$ and its poles: the total ramification over the values in $B$ together with the ramification at the poles equals $2g - 2 + 2n$, with $g$ the dimension of the space of regular differentials and $n = [F : \mathbb{C}(x)]$ the degree. It is obtained from the formulation as an infinite sum of $e_w - 1$ over all places, and is used in the construction of a paired cell family ([`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily)), where the count of ramification over an explicitly chosen finite set of values is what is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_sum_ramification_evalAt_eq.lean

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IntermediateField

theorem AlgebraicCurve.Place.sum_ramification_evalAt_eq {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [HasCanonicalDivisor (K := ℂ) (F := F)]
    {x : F} (htr : Transcendental ℂ x) [FiniteDimensional (↥(adjoin ℂ ({x} : Set F))) F]
    (B : Finset ℂ)
    (hB : ∀ (b : ℂ) (w : Place ℂ F), x ∈ w.toValuationSubring → Place.evalAt w x = b →
      (w.ord (x - algebraMap ℂ F b)).toNat ≠ 1 → b ∈ B)
    (t : ℂ → Finset (Place ℂ F))
    (ht : ∀ b ∈ B, ∀ w : Place ℂ F, w ∈ t b ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b)
    (p : Finset (Place ℂ F)) (hp : ∀ w : Place ℂ F, w ∈ p ↔ x ∉ w.toValuationSubring) :
    (∑ b ∈ B, ∑ w ∈ t b, (((w.ord (x - algebraMap ℂ F b)).toNat : ℤ) - 1)) +
        ∑ w ∈ p, (((w.ord x⁻¹).toNat : ℤ) - 1) =
      2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) - 2 +
        2 * (Module.finrank (↥(adjoin ℂ ({x} : Set F))) F : ℤ) := by sorry
