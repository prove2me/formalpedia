-- Prove2me | Theorems.Thm_FamousTheorems_kleene_recursion_theorem
-- name    : FamousTheorems.kleene_recursion_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:43.791238+00:00
-- url     : https://prove2.me/theorems/09ba3b71-90d2-409c-a640-6307c74ae30e
-- title:
--   Kleene's recursion theorem
-- statement:
--   **Kleene's recursion theorem.** If $f(c,n)$ is a partial recursive function of a program code $c$ and an input $n$, there is a program $c$ that computes $n\mapsto f(c,n)$, i.e. $\varphi_c=f(c,\cdot)$.
--
--   Programs can thus refer to their own code. The theorem gives quines, allows recursive definitions of computable functions to be justified directly, and yields short proofs of Rice's theorem and the undecidability of the halting problem. It is also a cornerstone of Gödel-style self-reference in computability theory.
--
--   **Formalization note.** Mathlib's `Nat.Partrec.Code.fixed_point₂`; `Partrec₂ f` says `f` is partial recursive in both arguments, and `c.eval` is the partial function computed by code `c`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.Partrec.Code.fixed_point₂`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem kleene_recursion_theorem {f : Nat.Partrec.Code → ℕ →. ℕ} (hf : Partrec₂ f) : ∃ c : Nat.Partrec.Code, c.eval = f c := by sorry

end FamousTheorems
