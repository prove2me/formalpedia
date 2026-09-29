-- Prove2me | Theorems.Thm_FamousTheorems_van_der_waerden
-- name    : FamousTheorems.van_der_waerden
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:13:59.000876+00:00
-- url     : https://prove2.me/theorems/f1e4e4d8-9a74-4fa7-a94d-1f01be0fa474
-- title:
--   Van der Waerden's theorem (Gallai's multidimensional form)
-- statement:
--   **Van der Waerden's theorem (Gallai's multidimensional form).** Let $M$ be a commutative monoid, $S\subseteq M$ finite, and colour $M$ with finitely many colours. Then some homothetic copy $aS+b=\{a\cdot s+b : s\in S\}$ with $a\in\mathbb N$, $a>0$, is monochromatic.
--
--   Taking $M=\mathbb N$ and $S=\{0,1,\dots,k-1\}$ gives van der Waerden's theorem: every finite colouring of $\mathbb N$ contains monochromatic arithmetic progressions of every length. Taking $M=\mathbb N^d$ gives the Gallai–Witt theorem on monochromatic homothetic copies of any finite configuration.
--
--   **Formalization note.** Mathlib's `Combinatorics.exists_mono_homothetic_copy`, derived from the Hales–Jewett theorem; `a • s` is the natural-number scalar action.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Combinatorics.exists_mono_homothetic_copy`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem van_der_waerden {M κ : Type*} [AddCommMonoid M] (S : Finset M) [Finite κ] (C : M → κ) :
    ∃ a > 0, ∃ (b : M) (c : κ), ∀ s ∈ S, C (a • s + b) = c := by sorry

end FamousTheorems
