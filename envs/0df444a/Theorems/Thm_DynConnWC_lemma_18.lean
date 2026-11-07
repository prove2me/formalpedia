-- Prove2me | Theorems.Thm_DynConnWC_lemma_18
-- name    : DynConnWC.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:12.751212+00:00
-- url     : https://prove2.me/theorems/d0eb45a6-1c60-4ec7-8165-69f3e35dff63
-- title:
--   Lemma 18 — $\Pr[\text{not }E_1]\le T_0Le^{-k/256}$
-- statement:
--   For a fixed valid update sequence with at most $T_0$ updates, let $E_1$ be the event that, for every update $t$ and level $i$, if $F_{i-1}\subseteq G$ at the merge step of level $i$ and $D(F_{i-1})\ge h$, then $S_i\ge D(F_{i-1})/64$ at that merge step. Then
--   $$\Pr[\text{not }E_1]\le T_0Le^{-k/256}.$$
--   It applies Lemma 11 at every level throughout the sequence.
--
--   Differences from the source:
--   - generalization: the data structure of §3 with the Euler-tour search of Appendix B.2 → any function of the two forests and two vertices meeting Lemma 7's specification, and any search mode; reason: the analysis uses only the specification and determinism; B.2's search with the plain mode is one instance
--   - generalization: $T_0=\lceil n^d\rceil$ → any $T_0$ at least the number of updates; reason: the bound and its proof use only that $T_0$ bounds the updates; $T_0=\lceil n^d\rceil$ is one instance
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 18, p.20 (PDF 21)

import Mathlib
import Definitions.Def_DynConnWC_Events

set_option autoImplicit false

namespace DynConnWC

/-- **Lemma 18 (Many successful searches at every level).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.20 (PDF 21).
"Let E1 be the event that, for every update t and every level i, if F_{i−1} ⊆ G at the merge step of
level i and D(F_{i−1}) ≥ h, then S_i ≥ D(F_{i−1})/64 at that merge step. Then
Pr[not E1] ≤ T0 L e^{−k/256}."

**Formalization Note.** The sequence is fixed in advance, valid, with at most `T0` updates. -/
theorem lemma_18 {n : ℕ} (hn : 2 ≤ n) (S : AlgSetup n) (hS : S.Wf)
    (σ : List (PunctSketch.Update n)) (hσ : PunctSketch.IsValidStream σ) (T0 : ℕ)
    (hT0 : σ.length ≤ T0) :
    probR S {R | ¬ E1 S R σ} ≤ (T0 : ℝ) * Lpar n * Real.exp (-(S.k : ℝ) / 256) := by sorry

end DynConnWC
