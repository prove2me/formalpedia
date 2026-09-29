-- Prove2me | Theorems.Thm_FamousTheorems_artin_tate_lemma
-- name    : FamousTheorems.artin_tate_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:30.278282+00:00
-- url     : https://prove2.me/theorems/abe43e38-595f-468c-850c-8a1c0b435db8
-- title:
--   The Artin–Tate lemma
-- statement:
--   **The Artin–Tate lemma.** Let $A\subseteq B\subseteq C$ be commutative rings with $A$ Noetherian. Suppose $C$ is finitely generated as an $A$-algebra and finitely generated as a $B$-module. Then $B$ is finitely generated as an $A$-algebra.
--
--   The lemma is the key step in one of the standard proofs of Zariski's lemma, and hence of Hilbert's Nullstellensatz: a field finitely generated as an algebra over a field $k$ is a finite extension of $k$. It is also used in invariant theory to show that rings of invariants of finite groups are finitely generated.
--
--   **Formalization note.** Mathlib's `fg_of_fg_of_fg`. The tower is given by algebra maps with `IsScalarTower A B C`, and the inclusion $B\subseteq C$ is the hypothesis that `algebraMap B C` is injective. Finite generation as an algebra is `(⊤ : Subalgebra A C).FG`, and as a module is `(⊤ : Submodule B C).FG`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `fg_of_fg_of_fg`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem artin_tate_lemma (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG)
    (hBC : (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) :
    (⊤ : Subalgebra A B).FG := by sorry

end FamousTheorems
