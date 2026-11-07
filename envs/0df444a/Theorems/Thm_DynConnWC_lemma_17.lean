-- Prove2me | Theorems.Thm_DynConnWC_lemma_17
-- name    : DynConnWC.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:34.92485+00:00
-- url     : https://prove2.me/theorems/67557648-bfe3-4b4f-9742-29f4194e51bf
-- title:
--   Lemma 17 — one link per level: the two deficit cases
-- statement:
--   Consider level $i$ in update $t$, for every outcome of the random choices.
--
--   1. If level $i$ links a pair in update $t$, then $D_i(t)\le D_i(t-1)$.
--   2. If level $i$ links no pair, and $F_{i-1},F_i\subseteq G$ at the merge step of level $i$, then
--   $$D_i(t)\le D_{i-1}(t)-\frac{S_i}2,$$
--   where $S_i$ counts the lower trees whose search returns a pair at that merge step.
--
--   These two cases are the induction step of the deficit invariant.
--
--   Differences from the source:
--   - generalization: the data structure of §3 with the Euler-tour search of Appendix B.2 → any function of the two forests and two vertices meeting Lemma 7's specification, and any search mode; reason: the analysis uses only the specification and determinism; B.2's search with the plain mode is one instance
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 17, p.20 (PDF 21)

import Mathlib
import Definitions.Def_DynConnWC_Events

set_option autoImplicit false

namespace DynConnWC

/-- **Lemma 17 (One link per level).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.20 (PDF 21).
"Consider level i in update t. 1. If level i links a pair in update t, then D_i(t) ≤ D_i(t − 1).
2. If level i links no pair, and F_{i−1}, F_i ⊆ G at the merge step of level i, then
D_i(t) ≤ D_{i−1}(t) − S_i/2, where S_i counts the lower trees whose search returns a pair at that merge
step."

**Formalization Note.** Every `R`, every setup meeting the standing assumptions, every valid sequence.
Case 1 has no hypothesis `F_i ⊆ G`, as on the page. -/
theorem lemma_17 {n : ℕ} (hn : 2 ≤ n) (S : AlgSetup n) (hS : S.Wf) (R : RandChoices S)
    (σ : List (PunctSketch.Update n)) (hσ : PunctSketch.IsValidStream σ) (t i : ℕ)
    (ht1 : 1 ≤ t) (ht : t ≤ σ.length) (hi1 : 1 ≤ i) (hi : i ≤ Lpar n) :
    ((recAt S R σ t i).linked = true → Dlev S R σ i t ≤ Dlev S R σ i (t - 1)) ∧
    ((recAt S R σ t i).linked = false →
      SubG (recAt S R σ t i).lowerAtMerge (Gt σ t) →
      SubG (recAt S R σ t i).upperAtMerge (Gt σ t) →
      (Dlev S R σ i t : ℝ) ≤ (Dlev S R σ (i - 1) t : ℝ) - (Smerge S R σ t i : ℝ) / 2) := by sorry

end DynConnWC
