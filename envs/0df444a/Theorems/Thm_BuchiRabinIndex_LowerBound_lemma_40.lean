-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_40
-- name    : BuchiRabinIndex.LowerBound.lemma_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:43.1392+00:00
-- url     : https://prove2.me/theorems/43eed60e-46e1-4f54-9598-4a65d1a79412
-- title:
--   Lemma 40 — witness walks
-- statement:
--   Let $n\ge1$, let $S$ be a clique of $G_n$, and let $x\in S$. For every distinct $y\in S$ outside $C(x)$, put $U=C(x)\cup C(y)$ and list $C(y)\setminus C(x)=\{z_1\prec_{\rm pre}\cdots\prec_{\rm pre}z_r\}$.
--
--   The explicitly constructed word $W_x^y$ is a closed walk at $t_x=H(C(x))$ visiting $H(U)$. Its unstable names are exactly $C(y)\setminus C(x)$, including $y$. Every node accepting anywhere on it equals $x$, and acceptance somewhere implies
--   $$|U|=n\quad\text{and}\quad y\prec_{\rm pre}x.$$
--   No name in $C(x)$ is unstable anywhere on $W_x$. Finally,
--   $$C_x=W_x\cup A_x\text{ is an accepting cycle}.$$
--
--   The cycle conclusion and the stability assertion are stated for every $x\in S$, including singleton cliques. The words, permutations and transition sets are computed by the definition layer.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: states q_1,...,q_n and alphabet 2^(Q×Q) → Fin n with q_i represented by i−1 and Finset transition relations; reason: this is a bijective indexing of all states and letters
--   - encoding: labels are functions defined on the node set → labels extend by the empty set outside the node set, with a validity subtype; reason: the extension is unique and adds no histories or transitions
--   - encoding: deterministic transitions may fail to have a successor → Option history trees, with a dying trace rejected by every condition; reason: root deletion has no history-tree successor; no sink is added
--   - reading: step 4 calls nodes whose descendants are deleted accepting → only the topmost resetting nodes survive to receive accepting annotations; reason: a nested reset below one of these nodes is deleted and any old such node is unstable
--   - encoding: the unique n-full ordered tree of Definition 12 → the explicitly enumerated positive words of weight at most n−1; reason: this is the same finite tree; no size is fixed
--   - generalization: Lemma 40 is printed under distinct x,y in S with y outside C(x) → the C_x accepting-cycle and C(x)-stability conclusions hold for every x in S, including singleton cliques; reason: these conclusions concern x alone, and the accepting loop A_x provides the singleton witness; the full printed case is included
--   - encoding: sets of actual history-tree transitions → sets in the ambient carrier of history/letter/history triples, with actual successors enforced in traces and cycles; reason: nonactual triples never occur in a trace or cycle; source transition sets embed unchanged
--   - encoding: the canonical histories H(T) used by the witness construction → the optional validity-checked Htree constructor, used at the specified chain and union trees; reason: the clique hypotheses ensure these trees are nonempty, ordered and have at most n nodes; Lemma 40 explicitly concludes constructor success, and no replacement history is introduced
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Lemma 40, p. 28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Witness

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, lemma 40; statement only. -/
theorem lemma_40 (n : ℕ) (hn : 1 ≤ n) (S : Finset Node)
    (hS : S ⊆ fullTree n) (hclique : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Adj n x y)
    (x : Node) (hx : x ∈ S) :
    (∀ y ∈ S, x ≠ y → y ∉ chain x →
      (∃ H K, Htree n (chain x) = some H ∧
        Htree n (chain x ∪ chain y) = some K ∧
        ClosedWalk (fullBuchi n hn) H (connectingWord n hn x y) ∧
        K ∈ visited (fullBuchi n hn) H (connectingWord n hn x y)) ∧
      (∀ z, (∃ e ∈ Wxy n hn x y, z ∈ unst (fullBuchi n hn) e) ↔
        z ∈ chain y \ chain x) ∧
      (∃ e ∈ Wxy n hn x y, y ∈ unst (fullBuchi n hn) e) ∧
      (∀ e ∈ Wxy n hn x y, ∀ z ∈ acc (fullBuchi n hn) e, z = x) ∧
      ((∃ e ∈ Wxy n hn x y, x ∈ acc (fullBuchi n hn) e) →
        (chain x ∪ chain y).card = n ∧ PreLt y x)) ∧
    (∀ e ∈ Wx n hn S x, ∀ z ∈ chain x, z ∉ unst (fullBuchi n hn) e) ∧
    AcceptingCycle (fullBuchi n hn) (Ccycle n hn S x) := by sorry

end BuchiRabinIndex.LowerBound
