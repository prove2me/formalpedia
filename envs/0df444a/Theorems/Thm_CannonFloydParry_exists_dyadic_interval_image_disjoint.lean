-- Prove2me | Theorems.Thm_CannonFloydParry_exists_dyadic_interval_image_disjoint
-- name    : CannonFloydParry.exists_dyadic_interval_image_disjoint
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-16T12:14:48.782214+00:00
-- url     : https://prove2.me/theorems/1a38ce69-e40f-4a23-b1de-9aae5db81ef5
-- title:
--   A nontrivial element of $F$ pushes a dyadic interval off itself
-- statement:
--   Let $f$ be an element of Thompson's group $F$, realised as an order isomorphism of the unit interval $[0,1]$, and suppose $f \neq 1$. Then there is a closed interval
--   $$[a,b] \subseteq (0,1), \qquad 0 < a < b < 1,$$
--   with **dyadic rational** endpoints which $f$ moves completely off itself:
--   $$f([a,b]) \cap [a,b] = \varnothing .$$
--   In the formal statement this disjointness is written pointwise: for every $z \in [0,1]$ with $a \le z \le b$ one has $f(z) \notin [a,b]$.
--
--   The statement is an existence assertion about a single nontrivial group element, and it is the geometric input to the simplicity argument for $[F,F]$: it produces an interval on which one may install auxiliary elements whose $f$-conjugates have disjoint support, so that the two families commute.
--
--   The mechanism is monotonicity. Since $f \neq 1$ there is a point $t \in [0,1]$ with $f(t) \neq t$. If $f(t) > t$, choose dyadic rationals $a, b$ with
--   $$t < a < b < f(t);$$
--   then $a > 0$ because $t \ge 0$, and $b < 1$ because $f(t) \le 1$, while for $z \in [a,b]$ monotonicity gives $f(z) > f(t) > b$, so $f(z) \notin [a,b]$. If $f(t) < t$, choose dyadic $a, b$ with $f(t) < a < b < t$ and argue symmetrically: for $z \in [a,b]$ one has $z < t$, hence $f(z) < f(t) < a$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Theorem 4.5, p. 230 (supporting step in the proof that the commutator subgroup of $F$ is simple)

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem exists_dyadic_interval_image_disjoint {f : UI ≃o UI} (hf : f ∈ F) (hf1 : f ≠ 1) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ IsDyadic a ∧ IsDyadic b ∧
      ∀ z : UI, (z : ℝ) ∈ Set.Icc a b → (f z : ℝ) ∉ Set.Icc a b := by
  sorry

end CannonFloydParry
