-- Prove2me | Theorems.Thm_FamousTheorems_ping_pong_lemma
-- name    : FamousTheorems.ping_pong_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:33.73765+00:00
-- url     : https://prove2.me/theorems/1e3a13e5-be9a-486c-8fa3-0d8152125581
-- title:
--   The ping-pong lemma
-- statement:
--   **The ping-pong lemma.** Let a group $G$ act on a set $\alpha$, and let $(H_i)_{i\in\iota}$ be groups with homomorphisms $f_i:H_i\to G$, where $\iota$ has at least two elements. Suppose there are nonempty, pairwise disjoint subsets $X_i\subseteq\alpha$ such that for all $i\ne j$ and all $h\in H_i$ with $h\ne1$, $f_i(h)\cdot X_j\subseteq X_i$. Assume also that $\iota$ has at least three elements or some $H_i$ has at least three elements. Then the induced homomorphism from the free product $\ast_i H_i$ to $G$ is injective.
--
--   The lemma, due to Klein, is the standard method for proving that given group elements generate a free group or a free product. It is used in the Tits alternative and to show that $\begin{pmatrix}1&2\\0&1\end{pmatrix}$ and $\begin{pmatrix}1&0\\2&1\end{pmatrix}$ generate a free subgroup of $SL_2(\mathbb Z)$.
--
--   **Formalization note.** Mathlib's `Monoid.CoprodI.lift_injective_of_ping_pong`. The free product is `Monoid.CoprodI H` and `Monoid.CoprodI.lift f` is the homomorphism induced by the $f_i$. The cardinality conditions are stated with `Cardinal.mk`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Monoid.CoprodI.lift_injective_of_ping_pong`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open Pointwise

theorem ping_pong_lemma {ι G : Type*} [Group G] {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G)
    (hcard : 3 ≤ Cardinal.mk ι ∨ ∃ i, 3 ≤ Cardinal.mk (H i)) {α : Type*} [MulAction G α] (X : ι → Set α)
    (hXne : ∀ i, (X i).Nonempty) (hXdisj : Pairwise (Function.onFun Disjoint X))
    (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i) [Nontrivial ι] :
    Function.Injective (Monoid.CoprodI.lift f) := by sorry

end FamousTheorems
