-- Prove2me | Theorems.Thm_FamousTheorems_acf_complete_6c
-- name    : FamousTheorems.acf_complete_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:49.530532+00:00
-- url     : https://prove2.me/theorems/759e6e8f-b088-455a-a537-3cf57b3089eb
-- title:
--   Completeness of the theory of algebraically closed fields of fixed characteristic
-- statement:
--   **Completeness of ACF$_p$.** Let $p$ be $0$ or a prime. The first-order theory of algebraically closed fields of characteristic $p$ is complete: for every sentence $\varphi$ in the language of rings, either $\varphi$ or $\neg\varphi$ follows from the theory.
--
--   The theorem is due to Tarski. Here it follows from the Łoś–Vaught test, since algebraically closed fields of a given characteristic and uncountable cardinality are determined up to isomorphism by that cardinality. It gives the Lefschetz principle: a first-order statement true in $\mathbb C$ is true in every algebraically closed field of characteristic $0$.
--
--   **Formalization note.** Mathlib's `FirstOrder.Field.ACF_isComplete`. `FirstOrder.Language.Theory.ACF p` is the theory in the language of rings with the field axioms, the axioms for characteristic $p$, and the axioms saying that every nonconstant monic polynomial has a root. `IsComplete` means that the theory is satisfiable and every sentence or its negation is a consequence.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FirstOrder.Field.ACF_isComplete`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem acf_complete_6c {p : ℕ} (hp : p.Prime ∨ p = 0) : (FirstOrder.Language.Theory.ACF p).IsComplete := by sorry

end FamousTheorems
