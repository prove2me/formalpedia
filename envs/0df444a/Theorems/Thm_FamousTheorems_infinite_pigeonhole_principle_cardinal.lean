-- Prove2me | Theorems.Thm_FamousTheorems_infinite_pigeonhole_principle_cardinal
-- name    : FamousTheorems.infinite_pigeonhole_principle_cardinal
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:12.296454+00:00
-- url     : https://prove2.me/theorems/1902b9cf-fdc5-48c2-9cdb-d8be2a03e028
-- title:
--   The infinite pigeonhole principle
-- statement:
--   **The infinite pigeonhole principle.** Let $f:\beta\to\alpha$, where $\beta$ is infinite and $|\alpha|<\operatorname{cf}|\beta|$. Then some fibre $f^{-1}(a)$ has the full cardinality $|\beta|$.
--
--   When more than $|\alpha|$ pigeons go into $|\alpha|$ holes, the finite pigeonhole principle only guarantees two pigeons in one hole. For infinite cardinals the cofinality condition gives a hole holding as many pigeons as there are in total. For example, any map from $\mathbb N$ to a finite set has an infinite fibre, and any map from $\aleph_1$ to $\mathbb N$ has an uncountable fibre.
--
--   **Formalization note.** Mathlib's `Cardinal.infinite_pigeonhole`. `Cardinal.mk β` is $|\beta|$, and `(Cardinal.mk β).ord.cof` is the cofinality of the initial ordinal of $|\beta|$. The two types live in the same universe.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Cardinal.infinite_pigeonhole`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u

theorem infinite_pigeonhole_principle_cardinal {α β : Type u} (f : β → α) (hβ : Cardinal.aleph0 ≤ Cardinal.mk β)
    (hα : Cardinal.mk α < (Cardinal.mk β).ord.cof) :
    ∃ a : α, Cardinal.mk (f ⁻¹' {a}) = Cardinal.mk β := by sorry

end FamousTheorems
