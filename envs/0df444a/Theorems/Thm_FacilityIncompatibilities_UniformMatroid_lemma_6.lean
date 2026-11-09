-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_lemma_6
-- name    : FacilityIncompatibilities.UniformMatroid.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:31.938197+00:00
-- url     : https://prove2.me/theorems/d95ff848-5749-4aa4-ad72-4e124e6b5bf4
-- title:
--   Lemma 6 — supermodularity of the connection cost A(·)
-- statement:
--   Let $(V_C,V_F,d,f,\mathcal M)$ be an FL-MI instance and let $A(X)$ be the minimum connection cost of a feasible assignment to $X$, with $A(X)=\infty$ for infeasible $X$. For all $X,Y\subseteq V_F$,
--
--   $$A(X)+A(Y)\le A(X\cup Y)+A(X\cap Y).$$
--
--   The inequality holds for all pairs, including those with infeasible $X\cap Y$ (then the right side is $\infty$). It yields the diminishing-returns inequality (1) used in the add- and delete-move arguments of Lemmas 5 and 10.
--
--   Differences from the source:
--   - generalization: metric distances d on V_C ∪ V_F (Definition 1) → a pseudometric: d(x,x)=0, symmetry and the triangle inequality, distinct points may be at distance 0; reason: every metric satisfies these axioms, so every instance of the source is covered
--   - encoding: A(X) real-valued, A(X)=∞ when X is infeasible → A(X) in ℝ≥0∞, the infimum over feasible assignments (⊤ on infeasible sets); reason: Lean convention; the same values on every instance
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 6, printed p.5 / PDF p.6; proof printed pp.6–9 / PDF pp.7–10

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Model

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid

/-- **Lemma 6** (printed p.5 / PDF p.6): supermodularity of the connection cost,
`A(X) + A(Y) ≤ A(X ∪ Y) + A(X ∩ Y)` for all `X, Y ⊆ V_F` (with `A = ∞` on infeasible sets). -/
theorem lemma_6 {C F : Type*} [Fintype C] [Fintype F] [DecidableEq F] (I : Instance C F)
    (hI : I.Valid) (X Y : Finset F) :
    I.A X + I.A Y ≤ I.A (X ∪ Y) + I.A (X ∩ Y) := by sorry

end FacilityIncompatibilities.UniformMatroid
