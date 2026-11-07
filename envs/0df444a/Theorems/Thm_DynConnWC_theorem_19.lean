-- Prove2me | Theorems.Thm_DynConnWC_theorem_19
-- name    : DynConnWC.theorem_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:34.455884+00:00
-- url     : https://prove2.me/theorems/6a13966f-6ce0-4015-8f15-8852aad9d5ab
-- title:
--   Theorem 19 — on $E_1\cap E_2$: $D_i(t)\le\max\{nq^i,h\}$ and $D_L(t)\le h$
-- statement:
--   With $q=127/128$, $L=128\lceil\log_2n\rceil$ and $h=128k$, if the events $E_1$ and $E_2$ hold, then for every update $t$ (and the initial state) and every level $0\le i\le L$,
--   $$D_i(t)\le\max\{nq^i,h\},$$
--   and in particular $D_L(t)\le h$. This is invariant I3: the top forest misses only $O(\log n)$ edges.
--
--   Differences from the source:
--   - generalization: the data structure of §3 with the Euler-tour search of Appendix B.2 → any function of the two forests and two vertices meeting Lemma 7's specification, and any search mode; reason: the analysis uses only the specification and determinism; B.2's search with the plain mode is one instance
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Theorem 19, p.20 (PDF 21–22); §4.1, p.17 (PDF 18)

import Mathlib
import Definitions.Def_DynConnWC_Events

set_option autoImplicit false

namespace DynConnWC

/-- **Theorem 19 (Deficit invariant).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.20 (PDF 21–22).
"Assume that the events E1 of Lemma 18 and E2 of Lemma 15 hold. Then, for every update t and every
level i, D_i(t) ≤ max{nq^i, h}. In particular D_L(t) ≤ h, which is invariant I3."

**Formalization Note.** `q = 127/128`, `L = 128⌈log₂ n⌉`, `h = 128k` (§4.1, p.17). The bound covers
`t = 0` (the initial state) and level `i = 0` as well, as the proof on p.21 does. -/
theorem theorem_19 {n : ℕ} (hn : 2 ≤ n) (S : AlgSetup n) (hS : S.Wf) (R : RandChoices S)
    (σ : List (PunctSketch.Update n)) (hσ : PunctSketch.IsValidStream σ)
    (hE1 : E1 S R σ) (hE2 : E2 S R σ) :
    (∀ t, t ≤ σ.length → ∀ i, i ≤ Lpar n →
      (Dlev S R σ i t : ℝ) ≤ max ((n : ℝ) * qpar ^ i) (hpar S : ℝ)) ∧
    (∀ t, t ≤ σ.length → Dlev S R σ (Lpar n) t ≤ hpar S) := by sorry

end DynConnWC
