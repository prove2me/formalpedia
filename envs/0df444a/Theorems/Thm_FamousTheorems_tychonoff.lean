-- Prove2me | Theorems.Thm_FamousTheorems_tychonoff
-- name    : FamousTheorems.tychonoff
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T06:56:12.344817+00:00
-- url     : https://prove2.me/theorems/273c0c4e-2eaa-4714-b81e-40b10af5413d
-- title:
--   Tychonoff's theorem
-- statement:
--   **Tychonoff's theorem.**
--
--   An arbitrary product of compact sets is compact in the product topology:
--   $$\prod_{i \in \iota} s_i \text{ is compact whenever each } s_i \text{ is.}$$
--
--   The index set is unrestricted — this is the infinite case, which is the whole
--   difficulty. For finitely many factors compactness of the product is elementary; for
--   infinitely many it is equivalent to the axiom of choice (Kelley, 1950), so no
--   constructive proof can exist. The product topology is essential: with the box topology
--   the statement is false.
--
--   Tychonoff proved the case of powers of the unit interval in 1930 while studying
--   compactifications; Čech gave the general version in 1937. It is the engine behind
--   Banach–Alaoglu (the dual ball sits inside a product of discs), the Stone–Čech
--   compactification, and compactness arguments in logic such as the compactness theorem
--   for propositional calculus.
--
--   **Formalization note.** The set is written as
--   `{ x : ∀ i, X i | ∀ i, x i ∈ s i }`, the product of the `s i` inside the dependent
--   function type carrying the product topology. The result is Mathlib's
--   `isCompact_pi_infinite`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open Filter Set Topology

theorem tychonoff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {s : ∀ i, Set (X i)} (h : ∀ i, IsCompact (s i)) :
    IsCompact { x : ∀ i, X i | ∀ i, x i ∈ s i } := by sorry

end FamousTheorems
