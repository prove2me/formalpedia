-- Prove2me | Theorems.Thm_FOMCMonDep_theorem_5_1
-- name    : FOMCMonDep.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:50.235919+00:00
-- url     : https://prove2.me/theorems/b9db0bcf-552f-4df4-b8a3-85089ac36921
-- title:
--   Theorem 5.1 (Closure Theorem) — a polynomial-size $A^*$ whose small subsets define flips separating each $v\notin A$ from $A$
-- statement:
--   Let $\mathcal C$ be a monadically dependent class of (possibly infinite) graphs and $r\in\mathbb N$. There are $c,s\in\mathbb N$ such that for every $G\in\mathcal C$ and every finite $A\subseteq V(G)$ there is a set $A^*\subseteq V(G)$ of size $O_{\mathcal C,r}(|A|^c)$ such that for every vertex $v\notin A$ there are a set $S(v)\subseteq A^*$ with $|S(v)|\le s$ and an $S(v)$-flip $H$ of $G$ with
--   $$\mathrm{dist}_H(v,A)>r .$$
--
--   The Closure Theorem is a finitary analogue of a result for monadically stable classes; it is the main combinatorial input of the type bound (Theorem 4.4).
--
--   **Formalization Note** An $S(v)$-flip is a $\mathcal P_{S(v)}$-flip. $O_{\mathcal C,r}(|A|^c)$ is $a|A|^c+b$ with $a,b$ chosen after $\mathcal C,r$. $\mathrm{dist}_H(v,A)>r$ holds when $A=\emptyset$.
--
--   Differences from the source:
--   - encoding: a monadically dependent class of possibly infinite graphs (Part I) → AnyGraphClass (members on every vertex type) with MonDepAny; reason: the paper's definition with the witness graph on any type; Part I allows infinite graphs
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Theorem 5.1, p.17 (PDF 19)

import Mathlib
import Definitions.Def_FOMCMonDep_IsPFlip
import Definitions.Def_FOMCMonDep_MonDepAny

set_option autoImplicit false

namespace FOMCMonDep

/-- **Theorem 5.1 (Closure Theorem).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §5, p.17 (PDF 19); restated p.19 (PDF 21): "For
every monadically dependent graph class 𝒞 and radius r ∈ N there are some c, s ∈ N with the following property. For
every G ∈ 𝒞 and finite set A ⊆ V(G) there is a set A* ⊆ V(G) of size O_{𝒞,r}(|A|^c) such that for every vertex v ∉ A
there is a set S(v) ⊆ A* of size at most s and an S(v)-flip H with dist_H(v, A) > r."

**Formalization Note.** Part I (possibly infinite graphs, `AnyGraphClass`, `MonDepAny`). `O_{𝒞,r}(|A|^c)` is
`a · |A|^c + b`, `a, b` after `𝒞, r`; `A*` is finite. An `S(v)`-flip is a `𝒫_{S(v)}`-flip (p.12).
`dist_H(v, A) > r` is `r < dist_H(v, x)` for every `x ∈ A`, distances in `ℕ∞`. -/
theorem theorem_5_1 (𝒞 : AnyGraphClass) (h𝒞 : MonDepAny 𝒞) (r : ℕ) :
    ∃ c s : ℕ, ∃ a b : ℕ, ∀ (V : Type) (G : SimpleGraph V), G ∈ 𝒞 V → ∀ A : Set V, A.Finite →
      ∃ Astar : Set V, Astar.Finite ∧ Astar.ncard ≤ a * A.ncard ^ c + b ∧
        ∀ v : V, v ∉ A → ∃ S : Finset V, (S : Set V) ⊆ Astar ∧ S.card ≤ s ∧
          ∃ H : SimpleGraph V, IsPFlip G (atomicPartition G (S : Set V)) H ∧
            ∀ x ∈ A, (r : ℕ∞) < H.edist v x := by sorry

end FOMCMonDep
