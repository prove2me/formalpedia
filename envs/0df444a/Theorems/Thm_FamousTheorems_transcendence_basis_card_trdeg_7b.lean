-- Prove2me | Theorems.Thm_FamousTheorems_transcendence_basis_card_trdeg_7b
-- name    : FamousTheorems.transcendence_basis_card_trdeg_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:02.308616+00:00
-- url     : https://prove2.me/theorems/c7c12144-9d00-42e6-ae4a-4ba48c828c61
-- title:
--   Every transcendence basis has cardinality equal to the transcendence degree
-- statement:
--   **Every transcendence basis has the same cardinality.** Let $R$ be a nontrivial commutative ring and $A$ a commutative $R$-algebra without zero divisors. Then every transcendence basis of $A$ over $R$ has cardinality equal to the transcendence degree $\operatorname{trdeg}_R A$.
--
--   This is the analogue for algebraic independence of the invariance of dimension for vector spaces. It makes the transcendence degree a well-defined invariant, which is the dimension of the corresponding variety in algebraic geometry: for example $\operatorname{trdeg}_k k(X_1,\dots,X_n)=n$. For fields the proof uses an exchange lemma like the Steinitz exchange lemma.
--
--   **Formalization note.** Mathlib's `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`. A transcendence basis is an algebraically independent family $x:\iota\to A$ over which $A$ is algebraic, and `Algebra.trdeg R A` is defined as the supremum of the cardinalities of algebraically independent families. `Cardinal.lift` moves both sides to a common universe.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem transcendence_basis_card_trdeg_7b {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial R] [NoZeroDivisors A] {x : ι → A}
    (hx : IsTranscendenceBasis R x) :
    Cardinal.lift.{u_3} (Cardinal.mk ι) = Cardinal.lift.{u_1} (Algebra.trdeg R A) := by sorry

end FamousTheorems
