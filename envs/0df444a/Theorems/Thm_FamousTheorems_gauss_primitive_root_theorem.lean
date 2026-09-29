-- Prove2me | Theorems.Thm_FamousTheorems_gauss_primitive_root_theorem
-- name    : FamousTheorems.gauss_primitive_root_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:17.745003+00:00
-- url     : https://prove2.me/theorems/6ff2125d-924b-4da4-acab-6b0a4e314322
-- title:
--   Gauss's theorem on primitive roots
-- statement:
--   **Gauss's theorem on primitive roots.** For a positive integer $n$, the group $(\mathbb Z/n\mathbb Z)^\times$ is cyclic (that is, there is a primitive root modulo $n$) if and only if
--   $$n\in\{1,2,4\}\quad\text{or}\quad n=p^m\ \text{or}\ n=2p^m$$
--   for an odd prime $p$ and $m\ge1$.
--
--   Gauss proved this in the *Disquisitiones Arithmeticae* (1801). Primitive roots give discrete logarithms modulo $n$, the index calculus, and the structure of $n$-th power residues. They also underlie the Diffie–Hellman and ElGamal cryptosystems.
--
--   **Formalization note.** Mathlib's `ZMod.isCyclic_units_iff`. It also includes $n=0$, where `ZMod 0 = ℤ` has unit group $\{\pm1\}$, which is cyclic.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ZMod.isCyclic_units_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gauss_primitive_root_theorem (n : ℕ) :
    IsCyclic (ZMod n)ˣ ↔
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 ∨ ∃ p m : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ m ∧ (n = p ^ m ∨ n = 2 * p ^ m) := by sorry

end FamousTheorems
