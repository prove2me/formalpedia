-- Prove2me | Theorems.Thm_FamousTheorems_universal_partial_recursive_function_7a
-- name    : FamousTheorems.universal_partial_recursive_function_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:37.31682+00:00
-- url     : https://prove2.me/theorems/c357d345-4310-4fc7-814f-0bec05b1a8ae
-- title:
--   Existence of a universal partial recursive function
-- statement:
--   **Existence of a universal partial recursive function.** Let $c\mapsto\varphi_c$ be the standard enumeration of the partial recursive functions $\mathbb N\rightharpoonup\mathbb N$ by codes $c$. The evaluation function
--   $$(c,n)\mapsto\varphi_c(n)$$
--   is itself partial recursive.
--
--   This is Kleene's enumeration theorem, the recursion-theoretic analogue of Turing's universal machine. Together with the s-m-n theorem it underlies Kleene's recursion theorem, the undecidability of the halting problem and Rice's theorem.
--
--   **Formalization note.** Mathlib's `Nat.Partrec.Code.eval_part`. `Nat.Partrec.Code` is Mathlib's syntax of partial recursive function codes, with an encoding into $\mathbb N$. `Nat.Partrec.Code.eval c n` is the result, possibly undefined, of running code $c$ on input $n$. `Partrec₂` means partial recursive as a function of two arguments.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.Partrec.Code.eval_part`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem universal_partial_recursive_function_7a : Partrec₂ Nat.Partrec.Code.eval := by sorry

end FamousTheorems
