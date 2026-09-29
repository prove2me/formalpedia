-- Prove2me | Theorems.Thm_FamousTheorems_smn
-- name    : FamousTheorems.smn
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T07:10:15.141718+00:00
-- url     : https://prove2.me/theorems/97789018-46f8-40a2-ac72-a77f55850b71
-- title:
--   The s-m-n theorem
-- statement:
--   **The s-m-n theorem** (the parametrization theorem).
--
--   There is a computable function $f$ taking a program $c$ and a value $n$ to a program
--   $f(c,n)$ that runs $c$ with $n$ frozen as its first argument:
--   $$\varphi_{f(c,n)}(x) = \varphi_c\bigl(\langle n, x\rangle\bigr).$$
--
--   Partial application can be performed *effectively* on source code: specializing a program to
--   a fixed input is itself a computable transformation of programs, not merely something an
--   outside observer can do. The name comes from Kleene's original notation $S^m_n$, where the
--   function freezes $m$ of $n$ arguments.
--
--   Together with the universal machine it is one of the two pillars of computability theory:
--   the two combine to give Kleene's recursion theorem, Rice's theorem, and the standard
--   undecidability results. It is also the formal content behind currying in programming
--   languages, and the reason partial evaluation is possible at all.
--
--   **Formalization note.** `Nat.Partrec.Code` is the type of codes for partial recursive
--   functions, `eval` interprets a code, `Computable₂` is computability in two arguments, and
--   `Nat.pair` is the pairing function. The result is Mathlib's `Nat.Partrec.Code.smn`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

open Filter Set Topology DirectSum

theorem smn : ∃ f : Nat.Partrec.Code → ℕ → Nat.Partrec.Code, Computable₂ f ∧
    ∀ c n x, Nat.Partrec.Code.eval (f c n) x =
      Nat.Partrec.Code.eval c (Nat.pair n x) := by sorry

end FamousTheorems
