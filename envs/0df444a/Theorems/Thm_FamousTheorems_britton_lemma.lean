-- Prove2me | Theorems.Thm_FamousTheorems_britton_lemma
-- name    : FamousTheorems.britton_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:38.137906+00:00
-- url     : https://prove2.me/theorems/f405e363-b128-4e75-a472-90121f67b12b
-- title:
--   Britton's lemma
-- statement:
--   **Britton's lemma.** Let $G$ be a group, $A,B\le G$ subgroups and $\varphi:A\to B$ an isomorphism, and let $G^*=\langle G,t\mid t a t^{-1}=\varphi(a)\ (a\in A)\rangle$ be the HNN extension. If a reduced word $w$ (one containing no pinch $t a t^{-1}$ with $a\in A$ or $t^{-1}bt$ with $b\in B$) represents an element of $G$ in $G^*$, then $w$ contains no occurrence of $t^{\pm1}$.
--
--   Britton's lemma is the normal form theorem for HNN extensions. It gives the embedding of $G$ into $G^*$ and solves the word problem there. It is central to the Higman embedding theorem and to the construction of finitely presented groups with unsolvable word problem.
--
--   **Formalization note.** Mathlib's `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`. A reduced word is an element of `HNNExtension.NormalWord.ReducedWord G A B`, and its `toList` is the list of its $t^{\pm1}$-letters with the intermediate group elements. The hypothesis says that the product of the word lies in the image of $G$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem britton_lemma {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B) (w : HNNExtension.NormalWord.ReducedWord G A B)
    (hw : HNNExtension.NormalWord.ReducedWord.prod φ w ∈ (HNNExtension.of : G →* HNNExtension G A B φ).range) :
    w.toList = [] := by sorry

end FamousTheorems
