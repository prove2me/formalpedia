-- Prove2me | Theorems.Thm_Combinatorics_uniform_family_propertyB_of_bounded_incidence
-- name    : Combinatorics.uniform_family_propertyB_of_bounded_incidence
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T18:45:10.029986+00:00
-- url     : https://prove2.me/theorems/f0aaa057-7267-40e9-bf5d-704d5a895e5d
-- title:
--   Property B for uniform set families with bounded point incidence
-- statement:
--   Let X and I be finite sets, and let (B_i) indexed by I be a family of subsets of X. Suppose every B_i has the same positive cardinality m, and every point of X belongs to at most D members of the indexed family. If
--
--   $$4mD\,2^{1-m}<1,$$
--
--   then there exists a map c from X to {red, blue} such that every B_i contains a point of each color.
--
--   This is the bounded vertex-degree criterion for Property B (proper two-colorability) of a uniform hypergraph. It can be applied to arbitrary finite set families, including the auxiliary hypergraph whose vertices are r-subsets and whose edges are the collections of r-subsets contained in a k-set.
--
--   **Formalization Note.** The family is indexed, so repeated members are counted with multiplicity in the incidence bound. This imposes a possibly stronger degree hypothesis than removing repetitions. The displayed strict inequality is a sufficient version of the source's non-strict bound. Bool represents the two colors.
-- source:
--   Arkadev Chattopadhyay and Bruce A. Reed, Properly 2-Colouring Linear Hypergraphs, Section 2 (Basic Notions), printed page 3, Lemma 5 and the following hypergraph-colouring application. https://www.tcs.tifr.res.in/~arkadev/linearNew3.pdf . The formal statement uses a strict sufficient inequality and an indexed-family representation, with multiplicity counted in D.

import Mathlib

theorem Combinatorics.uniform_family_propertyB_of_bounded_incidence
    (X I : Type*) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (B : I → Finset X) (m D : ℕ)
    (hm : 0 < m)
    (hsize : ∀ i, (B i).card = m)
    (hdegree : ∀ x, (Finset.univ.filter (fun i => x ∈ B i)).card ≤ D)
    (hcond : (4 : ℝ) * (m : ℝ) * (D : ℝ) * (2 : ℝ) ^ (1 - (m : ℝ)) < 1) :
    ∃ c : X → Bool, ∀ i,
      (∃ x ∈ B i, c x = true) ∧ (∃ x ∈ B i, c x = false) := by sorry
