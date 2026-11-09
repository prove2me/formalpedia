-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_lemma_9
-- name    : FacilityIncompatibilities.UniformMatroid.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:22.297885+00:00
-- url     : https://prove2.me/theorems/22c4de28-4a33-4fae-bd7e-ba6d5fdca824
-- title:
--   Lemma 9 — connection cost of the image P: A(P) ≤ C + 2C*
-- statement:
--   Let $(V_C,V_F,d,f,\mathcal M)$ be an FL-MI instance, $S,O\subseteq V_F$, $\sigma_O$ a minimum-cost feasible assignment to $O$, and $\pi$ a feasible assignment to $S$ minimizing $W(\pi)=\sum_j d(\sigma_O(j),\pi(j))$. Let $P=\pi(V_C)$, $C=A(S)$ and $C^*=A(O)$. Then
--
--   $$A(P)\le C+2C^*.$$
--
--   This is the input of the delete-move bound $F(S\setminus P)\le 2C^*$ (Lemma 10).
--
--   Differences from the source:
--   - generalization: metric distances d on V_C ∪ V_F (Definition 1) → a pseudometric: d(x,x)=0, symmetry and the triangle inequality, distinct points may be at distance 0; reason: every metric satisfies these axioms, so every instance of the source is covered
--   - generalization: O a fixed globally optimal solution with optimal assignment σ_O (§2.1, printed p.5) → O any facility set with a minimum-cost feasible assignment σ_O (any feasible O); reason: §3 (printed p.13) states the analysis does not require optimality of O and uses it for a non-optimal O after rescaling; an optimum is a special case
--   - generalization: S the fixed locally optimal solution and π the tie-broken W-minimizer of §2.1 → S any facility set and π any feasible assignment to S minimizing W (no tie-breaking, no local optimality of S); reason: the §2.1 π is such a minimizer and the §2.1 S such a set, so the source's statement is the special case
--   - encoding: A(X) real-valued, A(X)=∞ when X is infeasible → A(X) in ℝ≥0∞, the infimum over feasible assignments (⊤ on infeasible sets); reason: Lean convention; the same values on every instance
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 9, printed p.9 / PDF p.10

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Compression

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid

/-- **Lemma 9** (printed p.9 / PDF p.10): with `σ_O` a minimum-cost feasible assignment to `O`
and `π` a feasible assignment to `S` minimizing `W`, the image `P = π(V_C)` satisfies
`A(P) ≤ C + 2C*`, i.e. `A(P) ≤ A(S) + 2 A(O)`. -/
theorem lemma_9 {C F : Type*} [Fintype C] [Fintype F] [DecidableEq F] (I : Instance C F)
    (hI : I.Valid) (S O : Finset F) (σO π : C → F)
    (hσO : I.IsOptAssignment O σO) (hπ : I.IsWMin S σO π) :
    I.A (assignImage π) ≤ I.A S + 2 * I.A O := by sorry

end FacilityIncompatibilities.UniformMatroid
