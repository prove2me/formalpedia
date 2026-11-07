-- Prove2me | Theorems.Thm_BorderD4_theorem_6_6
-- name    : BorderD4.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:56.5504+00:00
-- url     : https://prove2.me/theorems/7ace8b53-fb65-4db0-a4f8-c945c05bc711
-- title:
--   Theorem 6.6: trailing monomials in $\overline{C}_d(m,r)$ have small support
-- statement:
--   Let $F$ be a field of characteristic zero, not necessarily algebraically closed, with any fixed monomial order. Every nonzero $G\in\overline{C}_d(m,r)$ satisfies
--   $$|\mathrm{supp}(\mathrm{tm}(G))|=O\bigl(d(\log m+r)\bigr).$$
--   The constant is absolute. Set against Lemma 6.20, this is the step that yields the lower bound.
--
--   Differences from the source:
--   - encoding: the variables $u_1,\dots,u_M$ → an arbitrary finite index type; reason: any such type is a tuple up to renaming
--   - encoding: $O(\cdot)$ → an absolute constant chosen before $F$, the order, $d$, $m$, $r$, with the natural logarithm; reason: the proof gives the constant $e^3/(1-\ln 2)$ (p.52)
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.6, p.50

import Mathlib
import Definitions.Def_BorderD4_BorderCompClass
import Definitions.Def_BorderD4_tm
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries
universe u v

namespace BorderD4

/-- Theorem 6.6: over a field of characteristic zero, not necessarily algebraically closed, every nonzero `G` in the
border class `C̄_d(m, r)` satisfies `|supp(tm(G))| = O(d(log m + r))`, for any fixed monomial order.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.6, p.50 (the proof, p.52, gives the constant `e³/(1 − ln 2)`).

**Formalization Note** The `O` hides an absolute constant, chosen before `F`, `τ`, the monomial order, `d`, `m`, `r`. The
parameters `d`, `m`, `r` are positive integers, as in Definition 6.4. -/
theorem theorem_6_6 : ∃ A : ℝ, 0 < A ∧ ∀ {F : Type u} [Field F] [CharZero F] {τ : Type v} [Fintype τ]
    (ω : MonomialOrder τ) {d m r : ℕ}, 1 ≤ d → 1 ≤ m → 1 ≤ r →
    ∀ G ∈ BorderCompClass F τ d m r, G ≠ 0 →
      ((tm ω G).support.card : ℝ) ≤ A * d * (Real.log m + r) := by sorry

end BorderD4
