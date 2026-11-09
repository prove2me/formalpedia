-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_lemma_5
-- name    : FacilityIncompatibilities.UniformMatroid.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:40.558203+00:00
-- url     : https://prove2.me/theorems/b92cdbae-c87e-4bf0-beb7-99a3d6120713
-- title:
--   Lemma 5 — connection cost of a local optimum: C ≤ C* + F*
-- statement:
--   Let $(V_C,V_F,d,f,\mathcal M)$ be an FL-MI instance (opening costs need not be uniform), let $S$ be a locally optimal feasible facility set for the add/delete neighbourhood, and let $O$ be a feasible facility set. With $C=A(S)$, $C^*=A(O)$ and $F^*=F(O)=\sum_{i\in O}f_i$,
--
--   $$C\le C^*+F^*.$$
--
--   This bounds the connection cost of the local optimum; with Lemmas 10 and 15 it gives the $(1+\sqrt2)$ guarantee after rescaling opening costs.
--
--   Differences from the source:
--   - generalization: metric distances d on V_C ∪ V_F (Definition 1) → a pseudometric: d(x,x)=0, symmetry and the triangle inequality, distinct points may be at distance 0; reason: every metric satisfies these axioms, so every instance of the source is covered
--   - generalization: O a fixed globally optimal solution with optimal assignment σ_O (§2.1, printed p.5) → O any facility set with a minimum-cost feasible assignment σ_O (any feasible O); reason: §3 (printed p.13) states the analysis does not require optimality of O and uses it for a non-optimal O after rescaling; an optimum is a special case
--   - encoding: A(X) real-valued, A(X)=∞ when X is infeasible → A(X) in ℝ≥0∞, the infimum over feasible assignments (⊤ on infeasible sets); reason: Lean convention; the same values on every instance
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 5, printed p.5 / PDF p.6; proof printed pp.5–6 / PDF pp.6–7

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Model

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid

/-- **Lemma 5** (printed p.5 / PDF p.6): for a locally optimal `S` and a feasible comparison set
`O`, `C ≤ C* + F*`, i.e. `A(S) ≤ A(O) + F(O)`. -/
theorem lemma_5 {C F : Type*} [Fintype C] [Fintype F] [DecidableEq F] (I : Instance C F)
    (hI : I.Valid) (S O : Finset F) (hS : I.IsLocalOpt S) (hO : I.IsFeasible O) :
    I.A S ≤ I.A O + ENNReal.ofReal (I.openCost O) := by sorry

end FacilityIncompatibilities.UniformMatroid
