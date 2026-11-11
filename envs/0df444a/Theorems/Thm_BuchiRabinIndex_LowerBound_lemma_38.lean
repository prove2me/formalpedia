-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_38
-- name    : BuchiRabinIndex.LowerBound.lemma_38
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:28.724256+00:00
-- url     : https://prove2.me/theorems/86ecca07-9ba1-4e0c-8090-53e99b2f1138
-- title:
--   Lemma 38 — effect of letters
-- statement:
--   Let $H=\langle T,l\rangle$ be any simple history of $F_n$, $n\ge1$, with root state set $P$. The four source cases have the following exact effects.
--
--   1. If $q_n\notin P$ and $q_p\in P$, generation by $\mathrm{id}_P\cup\{(q_p,q_n)\}$ inserts the new rightmost child of the node owning $q_p$, with label $\{q_n\}$. Every old own set is unchanged; both annotation sets are empty.
--   2. Every injection $\pi:P\to Q\setminus\{q_n\}$ gives the image-labelled tree $\langle T,\pi\circ l\rangle$, with both annotation sets empty.
--   3. If a leaf $x$ has label $\{q_s\}$ and an injection $\pi:P\to Q$ sends $q_s$ to $q_n$, its image-labelled tree has accepting set exactly $\{x\}$ and unstable set empty.
--   4. For a youngest-child leaf $z$ labelled $\{q_s\}$, deletion has accepting set empty and unstable set exactly $\{z\}$. If $q_n\notin P\setminus\{q_s\}$, all other own sets stay fixed. Otherwise, when $q_n$ labels another leaf $x$, the primed deletion makes $x$ own $q_s$ and leaves every other surviving own set fixed.
--
--   Every successor is required to exist and remain simple. These are exact successor and annotation equations, not merely existence of some tree having the indicated shape.
--
--   In particular, the exact annotation pairs in cases G, P, A and D are
--   $$\bigl(\operatorname{acc},\operatorname{unst}\bigr)=(\varnothing,\varnothing),\ (\varnothing,\varnothing),\ (\{x\},\varnothing),\ (\varnothing,\{z\}),$$
--   respectively; the primed deletion has the same annotation pair as D.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: states q_1,...,q_n and alphabet 2^(Q×Q) → Fin n with q_i represented by i−1 and Finset transition relations; reason: this is a bijective indexing of all states and letters
--   - encoding: labels are functions defined on the node set → labels extend by the empty set outside the node set, with a validity subtype; reason: the extension is unique and adds no histories or transitions
--   - encoding: deterministic transitions may fail to have a successor → Option history trees, with a dying trace rejected by every condition; reason: root deletion has no history-tree successor; no sink is added
--   - reading: step 4 calls nodes whose descendants are deleted accepting → only the topmost resetting nodes survive to receive accepting annotations; reason: a nested reset below one of these nodes is deleted and any old such node is unstable
--   - encoding: injective maps with domain P → total maps on Fin n whose restrictions to P are injective; reason: the finite nonempty target admits an extension, and values off P are never used
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Lemma 38, p. 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Witness

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, lemma 38; statement only. -/
theorem lemma_38 (n : ℕ) (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H) :
    (∀ p ∈ stateSet H.val, lastState n hn ∉ stateSet H.val →
      Effect hn H (genLetter hn (stateSet H.val) p) (generatedData hn H.val p) ∅ ∅ ∧
      (∀ x ∈ H.val.nodes, own (generatedData hn H.val p) x = own H.val x) ∧
      (generatedData hn H.val p).label
        (owner H.val p ++ [degree H.val.nodes (owner H.val p) + 1]) = {lastState n hn}) ∧
    (∀ π : Fin n → Fin n,
      Set.InjOn π {q | q ∈ stateSet H.val} →
      (∀ q ∈ stateSet H.val, π q ≠ lastState n hn) →
      Effect hn H (permLetter (stateSet H.val) π) (mapData H.val π) ∅ ∅) ∧
    (∀ x s (π : Fin n → Fin n), Leaf H.val.nodes x → H.val.label x = {s} →
      Set.InjOn π {q | q ∈ stateSet H.val} → π s = lastState n hn →
      Effect hn H (permLetter (stateSet H.val) π) (mapData H.val π) {x} ∅) ∧
    (∀ z s, Leaf H.val.nodes z → Youngest H.val.nodes z → H.val.label z = {s} →
      (lastState n hn ∉ (stateSet H.val).erase s →
        Effect hn H (delLetter (stateSet H.val) s) (deletedData H.val z s) ∅ {z} ∧
        ∀ x ∈ H.val.nodes, x ≠ z → own (deletedData H.val z s) x = own H.val x) ∧
      (∀ x, x ≠ z → Leaf H.val.nodes x → H.val.label x = {lastState n hn} →
        lastState n hn ∈ (stateSet H.val).erase s →
        Effect hn H (delPrimeLetter hn (stateSet H.val) s)
          (deletedPrimeData hn H.val z s) ∅ {z} ∧
        own (deletedPrimeData hn H.val z s) x = {s} ∧
        ∀ u ∈ H.val.nodes, u ≠ z → u ≠ x →
          own (deletedPrimeData hn H.val z s) u = own H.val u)) := by sorry

end BuchiRabinIndex.LowerBound
