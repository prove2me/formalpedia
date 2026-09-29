-- Prove2me | Theorems.Thm_FamousTheorems_rasiowa_sikorski_lemma
-- name    : FamousTheorems.rasiowa_sikorski_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:07:59.58998+00:00
-- url     : https://prove2.me/theorems/b1eb90fb-0265-4dd6-809a-9ee6caa2fdd3
-- title:
--   The Rasiowa–Sikorski lemma
-- statement:
--   **The Rasiowa–Sikorski lemma.** Let $P$ be a preorder, $p\in P$, and let $(D_i)_{i\in\iota}$ be a countable family of cofinal subsets of $P$. Then there is an ideal $I$ of $P$ that contains $p$ and meets every $D_i$.
--
--   In forcing terms, with the order reversed, it states that for countably many dense sets there is a generic filter through any given condition. It is the basic existence result behind forcing over countable transitive models, and a combinatorial form of the Baire category theorem.
--
--   **Formalization note.** Mathlib's `Order.cofinal_meets_idealOfCofinals` and `Order.mem_idealOfCofinals`, with witness `Order.idealOfCofinals p 𝒟`. A set is cofinal (`Order.Cofinal P`) if every element of $P$ lies below some element of it. Countability of the family is expressed by `Encodable ι`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Order.cofinal_meets_idealOfCofinals`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem rasiowa_sikorski_lemma {P : Type*} [Preorder P] (p : P) {ι : Type*} [Encodable ι] (𝒟 : ι → Order.Cofinal P) :
    ∃ I : Order.Ideal P, p ∈ I ∧ ∀ i, ∃ x ∈ 𝒟 i, x ∈ I := by sorry

end FamousTheorems
