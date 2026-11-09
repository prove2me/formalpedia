-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_lemma_10
-- name    : FacilityIncompatibilities.UniformMatroid.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:13.377459+00:00
-- url     : https://prove2.me/theorems/213c836e-755a-4a7c-b790-81b33699ea9b
-- title:
--   Lemma 10 — opening cost outside the image: F(S \ P) ≤ 2C*
-- statement:
--   Let $(V_C,V_F,d,f,\mathcal M)$ be an FL-MI instance, $O\subseteq V_F$ with a minimum-cost feasible assignment $\sigma_O$, and let $S$ be a feasible facility set that is locally optimal with respect to delete moves. Let $\pi$ be a feasible assignment to $S$ minimizing $W(\pi)=\sum_j d(\sigma_O(j),\pi(j))$ and $P=\pi(V_C)$. With $C^*=A(O)$,
--
--   $$F(S\setminus P)\le 2C^*.$$
--
--   It bounds the opening cost of the facilities of $S$ outside the image $P$, for uniform and non-uniform opening costs alike.
--
--   Differences from the source:
--   - generalization: metric distances d on V_C ∪ V_F (Definition 1) → a pseudometric: d(x,x)=0, symmetry and the triangle inequality, distinct points may be at distance 0; reason: every metric satisfies these axioms, so every instance of the source is covered
--   - generalization: O a fixed globally optimal solution with optimal assignment σ_O (§2.1, printed p.5) → O any facility set with a minimum-cost feasible assignment σ_O (any feasible O); reason: §3 (printed p.13) states the analysis does not require optimality of O and uses it for a non-optimal O after rescaling; an optimum is a special case
--   - generalization: π the tie-broken W-minimizer of §2.1 → π any feasible W-minimizer to S (no tie-breaking); reason: the §2.1 π is a W-minimizer, so the source's statement is the special case
--   - encoding: the real inequality F(S \ P) ≤ 2C* → ENNReal.ofReal F(S \ P) ≤ 2 · A(O) in ℝ≥0∞; reason: F(S \ P) ≥ 0 and A(O) is finite since O has a feasible assignment; same inequality
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 10, printed p.9 / PDF p.10; proof printed pp.9–10 / PDF pp.10–11

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Compression

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid

/-- **Lemma 10** (printed p.9 / PDF p.10): let `P = π(V_C)`. If `S` is locally optimal with
respect to delete moves, then `F(S \ P) ≤ 2C*`, i.e. `F(S \ P) ≤ 2 A(O)`. -/
theorem lemma_10 {C F : Type*} [Fintype C] [Fintype F] [DecidableEq F] (I : Instance C F)
    (hI : I.Valid) (S O : Finset F) (σO π : C → F) (hS : I.IsDeleteLocalOpt S)
    (hσO : I.IsOptAssignment O σO) (hπ : I.IsWMin S σO π) :
    ENNReal.ofReal (I.openCost (S \ assignImage π)) ≤ 2 * I.A O := by sorry

end FacilityIncompatibilities.UniformMatroid
