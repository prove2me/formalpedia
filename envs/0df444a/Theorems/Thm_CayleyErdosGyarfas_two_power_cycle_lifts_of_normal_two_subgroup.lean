-- Prove2me | Theorems.Thm_CayleyErdosGyarfas_two_power_cycle_lifts_of_normal_two_subgroup
-- name    : CayleyErdosGyarfas.two_power_cycle_lifts_of_normal_two_subgroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T02:10:52.86904+00:00
-- url     : https://prove2.me/theorems/38fd4932-c24e-460b-89a6-f7421a1868de
-- title:
--   Lemma 1.3: power-of-two cycles lift through normal 2-subgroups
-- statement:
--   Let $G$ be a finite group and let $S \subseteq G$ be a generating set of $G$ that is closed under inverses and does not contain the identity. Let $P \trianglelefteq G$ be a normal $2$-subgroup, so that every element of $P$ has order a power of $2$, and write
--
--   $$\overline{S} = \{ sP : s \in S \} \setminus \{ P \} \subseteq G/P .$$
--
--   for the image of $S$ in $G/P$ with the identity coset removed. Then
--
--   $$\operatorname{Cay}(G/P, \overline{S}) \text{ has a cycle of length } 2^n \text{ for some } n \ge 2 \;\Longrightarrow\; \operatorname{Cay}(G,S) \text{ has a cycle of length } 2^m \text{ for some } m \ge 2 .$$
--
--   The exponents $n$ and $m$ may differ. Here, for a group $H$ and a subset $T \subseteq H$, $\operatorname{Cay}(H,T)$ is the Cayley graph with vertex set $H$ in which distinct $x, y \in H$ are adjacent when $y = xt$ or $x = yt$ for some $t \in T$; every left multiplication $z \mapsto hz$ is an automorphism of it. A cycle of length $k$ is a closed walk $(v_0, v_1, \dots, v_k = v_0)$ with $k \ge 3$ whose vertices $v_1, \dots, v_k$ are pairwise distinct.
--
--   No parity or size hypothesis is imposed on $G$ or $S$. The paper proves Corollary 1.4 from this lemma, Theorem 1.1 applied to the odd-order quotient by the Sylow $2$-subgroup, and the first two paragraphs of the proof of this lemma, which treat generators lying in $P$ and distinct generators with the same image in $G/P$.
--
--   **Formalization Note** The kernel hypotheses are `[P.Normal]` and `IsPGroup 2 P`, and the quotient generating set is `(QuotientGroup.mk (s := P)) '' S \ {1}`. The statement is identical, up to the spelling of the namespace, to `CayleyErdősGyárfás.two_power_cycle_lifts_of_normal_two_subgroup` in the Challenge of Palomar entry PALOMAR-2026-11-04-000015, where it is proved.
-- source:
--   M. C. Burkhart, Odd-ordered Cayley graphs satisfy Erdős–Gyárfás, arXiv:2611.05060v1 (3 Nov 2026), https://arxiv.org/abs/2611.05060v1, §1, p. 2, Lemma 1.3 (proof in §3, pp. 5–6); standing conventions of §1.1, p. 2; power-of-two length in the sense of §1, p. 1 (a simple cycle of length 2^n, n ≥ 2). Lean statement as in the Challenge of Palomar entry PALOMAR-2026-11-04-000015 (https://palomar-registry.org/entry?id=PALOMAR-2026-11-04-000015).

import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Card

namespace CayleyErdosGyarfas

/-- **Lemma 1.3** (arXiv:2611.05060v1, p. 2). Let `G = ⟨S⟩` be a finite group, with
`S` symmetric and `1 ∉ S`, and let `P` be a normal 2-subgroup. Put
`S̄ = {sP : s ∈ S} \ {P}`. If `Cay(G/P, S̄)` contains a simple cycle of length `2 ^ n`
with `n ≥ 2`, then `Cay(G, S)` contains a simple cycle of length `2 ^ m` with `m ≥ 2`;
the two exponents may differ. -/
theorem two_power_cycle_lifts_of_normal_two_subgroup
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P)
    (hcycle : ∃ (n : ℕ) (v : G ⧸ P)
      (c : (SimpleGraph.mulCayley
        ((QuotientGroup.mk (s := P)) '' S \ {1})).Walk v v),
      2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n) :
    ∃ (n : ℕ) (v : G) (c : (SimpleGraph.mulCayley S).Walk v v),
      2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by sorry

end CayleyErdosGyarfas
