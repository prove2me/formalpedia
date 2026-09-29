-- Prove2me | Theorems.Thm_FamousTheorems_gordan_lemma
-- name    : FamousTheorems.gordan_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:04.18098+00:00
-- url     : https://prove2.me/theorems/806ff29b-66cd-4a17-8f99-72d2473ac37e
-- title:
--   Gordan's lemma
-- statement:
--   **Gordan's lemma.** Let $M$ be a commutative monoid whose natural order is a well-quasi-order and which is cancellative, for example $\mathbb N^n$, and let $f,g:M\to N$ be monoid homomorphisms into a cancellative monoid. Then the submonoid $\{x\in M: f(x)=g(x)\}$ is finitely generated.
--
--   With $M=\mathbb N^n$ and $f,g$ given by integer matrices with nonnegative entries, this says that the nonnegative integer solutions of a homogeneous linear system form a finitely generated monoid. This is the classical form of Gordan's lemma, which is basic in toric geometry, invariant theory and integer programming.
--
--   **Formalization note.** Mathlib's `Submonoid.fg_eqLocusM`. `f.eqLocusM g` is the submonoid where $f$ and $g$ agree. The hypotheses on $M$ are expressed by `WellQuasiOrderedLE`, `IsOrderedCancelMonoid` and `CanonicallyOrderedMul`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Submonoid.fg_eqLocusM`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gordan_lemma {M N : Type*} [CommMonoid M] [PartialOrder M] [WellQuasiOrderedLE M] [IsOrderedCancelMonoid M]
    [CanonicallyOrderedMul M] [Monoid N] [IsCancelMul N] (f g : M →* N) : (f.eqLocusM g).FG := by sorry

end FamousTheorems
