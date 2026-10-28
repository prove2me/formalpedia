-- Prove2me | Theorems.Thm_CollapsibleCubics_exists_closed_cubic_transition_chain
-- name    : CollapsibleCubics.exists_closed_cubic_transition_chain
-- status  : Open
-- author  : @shivm
-- created : 2026-10-25T20:29:23.789842+00:00
-- url     : https://prove2.me/theorems/7c8d5ee9-39d1-4782-a918-fc6267faf5fa
-- title:
--   Open rational-cycle criterion for obstructed depressed cubics
-- statement:
--   Let $d,e\in\mathbb Q$ and suppose that
--
--   $$q(X)=X^3+dX+e$$
--
--   is irreducible over $\mathbb Q$, with
--
--   $$\nexists r,s\in\mathbb Q,\qquad r^2+rs+s^2=-d.$$
--
--   The open assertion is that there are an integer $n\ge1$, rational states $t_0,\ldots,t_n$, and rational controls $x_0,\ldots,x_{n-1}$ satisfying
--
--   $$t_n=t_0,\qquad
--   (t_i^2+t_ix_i+x_i^2+d)t_{i+1}
--    =t_i^2x_i+t_ix_i^2-e\quad(0\le i<n).$$
--
--   Equivalently, these data describe a nonempty closed chain for the rational transition
--
--   $$T_{d,e}(t,x)=\frac{t^2x+tx^2-e}{t^2+tx+x^2+d}.$$
--
--   The norm-form hypothesis ensures that its denominator is nonzero for all rational inputs. No bound is imposed on the length of the chain, and repeated states and controls are allowed.
--
--   This is the unresolved arithmetic/dynamical child in a proposed reduction of the split-representative problem. A chain supplies two rational linear factors per transition, so its existence would give a split representative of degree $2n$ modulo $q$. The implication from a closed chain to a split representative is verified in the parent submission; **existence of such a chain in general is not proved**. No converse or equivalence with general collapsibility is asserted here.
--
--   **Formalization Note** The states and controls are extended to functions on $\mathbb N$; only the displayed finite ranges are constrained. The recurrence is expressed without division.
-- source:
--   Prove2Me, Collapsible Cubics mission dc12281f-394d-46b0-aea9-a96fcb177a51, discussion comment 7bf60d1a-3a2e-4ee3-84b8-75918d716e34 by shivm, 2026-10-04, section 3(c), Cycles; accessible in https://prove2.me/api/v1/missions/dc12281f-394d-46b0-aea9-a96fcb177a51/comments . This is the explicitly open finite-chain existence assertion suggested by that transition identity, not an established result of the blog. Background: Miles, On collapsible algebraic numbers, sections Collapsible reduction and The cubic case, https://quesswho.github.io/miles-blog/2026/08/20/collapsible/ .

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.Rat

open Polynomial

namespace CollapsibleCubics

/-- The rational transition relation associated with a depressed cubic has a
nonempty closed chain in the case not covered by the Eisenstein norm form. -/
theorem exists_closed_cubic_transition_chain
    (d e : ℚ)
    (hirr : Irreducible (X ^ 3 + C d * X + C e : ℚ[X]))
    (hrep : ¬ ∃ r s : ℚ, r ^ 2 + r * s + s ^ 2 = -d) :
    ∃ n : ℕ, 0 < n ∧ ∃ t x : ℕ → ℚ,
      t n = t 0 ∧ ∀ i < n,
        (t i ^ 2 + t i * x i + x i ^ 2 + d) * t (i + 1) =
          t i ^ 2 * x i + t i * x i ^ 2 - e := by
  sorry

end CollapsibleCubics
