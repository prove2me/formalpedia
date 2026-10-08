-- Prove2me | Theorems.Thm_EdmondsPartition_Main_rado_rank
-- name    : EdmondsPartition.Main.rado_rank
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T15:23:23.767985+00:00
-- url     : https://prove2.me/theorems/1b363d40-6494-481b-9b13-628b5926cefb
-- title:
--   Rado's theorem for a monotone submodular integer rank function
-- statement:
--   Let $\iota$ be a finite index set and $\beta$ a type. Let $r$ be an integer-valued function on the finite subsets of $\beta$ that is **monotone** ($X\subseteq Y\Rightarrow r(X)\le r(Y)$), **submodular** ($r(X\cup Y)+r(X\cap Y)\le r(X)+r(Y)$) and satisfies $r(X)\le |X|$ (for example the rank function of a matroid). Let $(A_i)_{i\in\iota}$ be finite subsets of $\beta$ such that **Rado's condition** holds:
--   $$|J|\le r\Bigl(\bigcup_{i\in J}A_i\Bigr)\qquad\text{for every } J\subseteq\iota .$$
--   Then there are elements $a_i\in A_i$ $(i\in\iota)$ such that the set $\{a_i:i\in\iota\}$ has rank $r=|\iota|$.
--
--   Since $r(X)\le|X|$, the rank condition forces $|\{a_i\}|\ge|\iota|$, so the $a_i$ are pairwise distinct: they form an independent transversal when $r$ is a matroid rank function. This is Rado's theorem (1942). The proof is the standard shrinking argument: while some $A_i$ has two elements $y\ne z$, deleting $y$ or deleting $z$ preserves Rado's condition, by submodularity applied to two violating index sets; at the end every $A_i$ is a singleton.
--
--   **Formalization Note** Only monotonicity, submodularity and $r(X)\le|X|$ are assumed; neither $r(\varnothing)=0$ nor nonnegativity is needed. The conclusion is stated as $r(\{a_i\})=|\iota|$ so that it applies to any such rank function.
-- source:
--   R. Rado, A theorem on independence relations, Quart. J. Math. Oxford 13 (1942), 83-89 (Rado's theorem on independent transversals; the proof is the standard shrinking argument for a submodular rank function)

import Mathlib

namespace EdmondsPartition.Main

theorem rado_rank {ι β : Type*} [DecidableEq ι] [DecidableEq β] [Fintype ι]
    (r : Finset β → ℤ)
    (hmono : ∀ {X Y : Finset β}, X ⊆ Y → r X ≤ r Y)
    (hsub : ∀ X Y : Finset β, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)
    (hcard : ∀ X : Finset β, r X ≤ X.card)
    (A : ι → Finset β) (hA : ∀ J : Finset ι, (J.card : ℤ) ≤ r (J.biUnion A)) :
    ∃ a : ι → β, (∀ i, a i ∈ A i) ∧ r (Finset.univ.image a) = Fintype.card ι := by sorry

end EdmondsPartition.Main
