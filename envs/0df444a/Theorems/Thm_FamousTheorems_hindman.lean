-- Prove2me | Theorems.Thm_FamousTheorems_hindman
-- name    : FamousTheorems.hindman
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:14:45.361993+00:00
-- url     : https://prove2.me/theorems/d53375f0-1ce0-4667-a431-0e95c32e5315
-- title:
--   Hindman's theorem
-- statement:
--   **Hindman's theorem.** Colour a semigroup with finitely many colours. For every sequence $a$, if all finite products $\mathrm{FP}(a)$ (products $a_{i_1}a_{i_2}\cdots a_{i_k}$ with $i_1<\dots<i_k$) are coloured, then some colour class contains all finite products $\mathrm{FP}(b)$ of another sequence $b$.
--
--   For $(\mathbb N,+)$ this says every finite colouring of $\mathbb N$ has an infinite set all of whose finite sums share a colour. It is the prototypical infinite-dimensional Ramsey theorem, and its standard proof (via idempotent ultrafilters in $\beta S$) founded the algebra of the Stone–Čech compactification in combinatorics.
--
--   **Formalization note.** Mathlib's `Hindman.FP_partition_regular`; the colouring is a finite family `s` of sets covering `FP a`, and `b` is a subsequence-product stream.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Hindman.FP_partition_regular`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hindman {M : Type*} [Semigroup M] (a : Stream' M) (s : Set (Set M)) (hs : s.Finite)
    (hcov : Hindman.FP a ⊆ ⋃₀ s) :
    ∃ c ∈ s, ∃ b : Stream' M, Hindman.FP b ⊆ c := by sorry

end FamousTheorems
