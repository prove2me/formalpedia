-- Prove2me | Theorems.Thm_CayleyErdosGyarfas_odd_order_cayley_contains_two_power_cycle
-- name    : CayleyErdosGyarfas.odd_order_cayley_contains_two_power_cycle
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-11-12T02:10:45.602404+00:00
-- url     : https://prove2.me/theorems/f5be7850-6b64-485d-a383-155e4563fe64
-- title:
--   Theorem 1.1: Cayley graphs of odd-order groups satisfy Erdős–Gyárfás
-- statement:
--   Let $G$ be a finite group of odd order and let $S \subseteq G$ be a generating set of $G$ that is closed under inverses, does not contain the identity, and has at least three elements. Then the Cayley graph $\operatorname{Cay}(G,S)$ contains a cycle whose length is a power of two:
--
--   $$\exists\, n \ge 2 : \quad \operatorname{Cay}(G,S) \text{ contains a cycle of length } 2^n .$$
--
--   Here $\operatorname{Cay}(G,S)$ has vertex set $G$, distinct $g, h$ being adjacent when $h = gs$ or $g = hs$ for some $s \in S$, and a cycle of length $k$ is a closed walk $(v_0, v_1, \dots, v_k = v_0)$ with $k \ge 3$ whose vertices $v_1, \dots, v_k$ are pairwise distinct.
--
--   Under these hypotheses every vertex has exactly $|S|$ neighbours, so $|S| \ge 3$ says that the minimum degree is at least three. The theorem therefore states that Cayley graphs of groups of odd order satisfy the Erdős–Gyárfás conjecture. It is the main theorem of the paper.
--
--   **Formalization Note** Odd order is `Odd (Nat.card G)` with `[Finite G]`, generation is `Subgroup.closure S = ⊤`, and $|S|$ is `S.ncard`. The graph is Mathlib's `SimpleGraph.mulCayley S` and a cycle is a closed walk with `IsCycle`. The bound $n \ge 2$ is kept to match the paper, although cycles have length at least $3$. The hypothesis $1 \notin S$ is needed: in the cyclic group $C_3 = \langle a \rangle$ the set $\{1, a, a^{-1}\}$ is symmetric, generates $C_3$ and has three elements, but its Cayley graph is a triangle. The statement is identical, up to the spelling of the namespace, to `CayleyErdősGyárfás.odd_order_cayley_contains_two_power_cycle` in the Challenge of Palomar entry PALOMAR-2026-11-04-000015, where it is proved.
-- source:
--   M. C. Burkhart, Odd-ordered Cayley graphs satisfy Erdős–Gyárfás, arXiv:2611.05060v1 (3 Nov 2026), https://arxiv.org/abs/2611.05060v1, §1, p. 1, Theorem 1.1 (proof in §2, pp. 4–5); standing conventions of §1.1, p. 2. Lean statement as in the Challenge of Palomar entry PALOMAR-2026-11-04-000015 (https://palomar-registry.org/entry?id=PALOMAR-2026-11-04-000015).

import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Card

namespace CayleyErdosGyarfas

/-- **Theorem 1.1** (arXiv:2611.05060v1, p. 1). If `G` is a finite group of odd order
and `S` is a symmetric generating set with `1 ∉ S` and `|S| ≥ 3`, then the Cayley graph
`Cay(G, S)` contains a simple cycle of length `2 ^ n` for some `n ≥ 2`. -/
theorem odd_order_cayley_contains_two_power_cycle
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G))
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (SimpleGraph.mulCayley S).Walk v v),
      2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by sorry

end CayleyErdosGyarfas
