-- Prove2me | Theorems.Thm_FamousTheorems_real_least_upper_bound_7b
-- name    : FamousTheorems.real_least_upper_bound_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:55.0059+00:00
-- url     : https://prove2.me/theorems/ba1e83d9-db7b-4cfa-8b3c-55f26210550b
-- title:
--   The least upper bound property of the real numbers
-- statement:
--   **The least upper bound property of $\mathbb R$.** Every nonempty set of real numbers that is bounded above has a least upper bound.
--
--   This is the completeness axiom of the real numbers, and it distinguishes $\mathbb R$ from $\mathbb Q$: the set $\{x\in\mathbb Q:x^2<2\}$ has no least upper bound in $\mathbb Q$. The basic theorems of real analysis all rest on it, including the intermediate value theorem, the extreme value theorem, the Bolzano–Weierstrass theorem and the convergence of bounded monotone sequences. In Mathlib it is a theorem about the construction of $\mathbb R$ by Cauchy sequences.
--
--   **Formalization note.** Mathlib's `Real.exists_isLUB`. `IsLUB s x` says that $x$ is an upper bound of $s$ and is below every upper bound of $s$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.exists_isLUB`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem real_least_upper_bound_7b {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ x : ℝ, IsLUB s x := by sorry

end FamousTheorems
