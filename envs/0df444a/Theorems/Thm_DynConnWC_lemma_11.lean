-- Prove2me | Theorems.Thm_DynConnWC_lemma_11
-- name    : DynConnWC.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:33:32.34197+00:00
-- url     : https://prove2.me/theorems/58c1f3d4-629d-48a2-a16d-2b4c22949d62
-- title:
--   Lemma 11 — $N\ge128k\Rightarrow\Pr[\text{fewer than }N/64\text{ searches return a pair}]\le e^{-k/256}$
-- statement:
--   Let $k\ge2$ be even, $G$ a graph on $V$, and $\mathcal P$ a partition of $V$, with $N$ the number of parts with nonempty cutset. If $N\ge128k$, then:
--
--   1. For every law of labelings whose labels of any at most $k$ distinct potential edges are independent and uniform $J$-bit strings,
--   $$\Pr\big[|\{P\in\mathcal P:\text{some threshold selects exactly one edge of }\delta_G(P)\}|<N/64\big]\le e^{-k/256}.$$
--   2. For one instance of the cutset structure with uniform random choices and $w\ge J$,
--   $$\Pr\big[|\{P\in\mathcal P:\mathrm{search}(P)\ne\bot\}|<N/64\big]\le e^{-k/256}.$$
--
--   The bound lets one instance serve many trees at a level although their searches are dependent.
--
--   Differences from the source:
--   - generalization: the labels of the polynomial $H$; a partition into the trees of the maintained forest → clause 1: any $k$-wise independent uniform labeling and the event that some threshold selects exactly one cut edge; any partition; reason: the proof uses only that event and that hypothesis; clause 2 states the source's form for the polynomial construction, in every search mode
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 11, pp.15–16 (PDF 16–17)

import Mathlib
import Definitions.Def_DynConnWC_Cutset

set_option autoImplicit false

namespace DynConnWC

open Classical in
/-- **Lemma 11 (Many searches return a pair).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), pp.15–16 (PDF 16–17).
"Fix a graph G and a partition P of V into the trees of the forest maintained by the cutset instance,
independently of the instance's random choices. Let N be the number of trees in P with nonempty graph
cutsets. If N ≥ 128k, then Pr[|{P ∈ P : search(P) ≠ ⊥}| < N/64] ≤ e^{−k/256}."

**Formalization Note.** The first clause is for any law of labelings whose labels are `k`-wise
independent and uniform (`KWiseUniform`), with the event "some threshold selects exactly one edge of
the cut of `P`". The second clause is the statement for one instance of the cutset structure, with
its uniform random choices and its search, in any search mode; it needs `w ≥ J` so that identifiers
are distinct field elements. The partition is any partition of `Fin n`: every partition is the
family of trees of some forest. -/
theorem lemma_11 {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (hk2 : 2 ≤ k) (hk : Even k)
    (G : SimpleGraph (Fin n)) (P : Finpartition (Finset.univ : Finset (Fin n)))
    (hN : 128 * k ≤ (P.parts.filter (fun T => (cutset G T).Nonempty)).card) :
    (∀ μ : PMF (Sym2 (Fin n) → Fin (2 ^ Jbits n)), KWiseUniform k μ →
      (μ.toOuterMeasure {lab |
        (((P.parts.filter (fun T =>
            SomeThresholdSelectsOne (fun e => (lab e : ℕ)) (cutset G T))).card : ℕ) : ℝ) <
          ((P.parts.filter (fun T => (cutset G T).Nonempty)).card : ℝ) / 64}).toReal ≤
        Real.exp (-(k : ℝ) / 256)) ∧
    (∀ (w : ℕ), Jbits n ≤ w → ∀ (enc : GaloisField 2 w ≃ BitVec w) (mode : SearchMode),
      ((coinLaw w k).toOuterMeasure {co |
        (((P.parts.filter (fun T => (search mode enc co G T).isSome)).card : ℕ) : ℝ) <
          ((P.parts.filter (fun T => (cutset G T).Nonempty)).card : ℝ) / 64}).toReal ≤
        Real.exp (-(k : ℝ) / 256)) := by sorry

end DynConnWC
