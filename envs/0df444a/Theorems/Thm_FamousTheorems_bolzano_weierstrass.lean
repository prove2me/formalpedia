-- Prove2me | Theorems.Thm_FamousTheorems_bolzano_weierstrass
-- name    : FamousTheorems.bolzano_weierstrass
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T07:14:51.418494+00:00
-- url     : https://prove2.me/theorems/6876ca84-ab3c-4749-a4bd-66a0a674a410
-- title:
--   The Bolzano–Weierstrass theorem
-- statement:
--   **The Bolzano–Weierstrass theorem.**
--
--   In a proper metric space, every sequence taking values in a bounded set has a subsequence
--   converging to a point of the closure:
--   $$\exists\, a \in \overline{s},\ \exists\, \varphi \text{ strictly increasing},\ x_{\varphi(n)} \to a.$$
--
--   Boundedness alone buys convergence, provided one is allowed to discard terms. For
--   $\mathbb{R}$ this is the classical statement, proved by repeated bisection: halve the
--   interval, keep a half containing infinitely many terms, repeat. The limit point need not lie
--   in $s$ itself, only in its closure, which is why the closure appears in the statement.
--
--   It is one of the standard equivalent formulations of completeness of the reals, alongside
--   the least upper bound property, Cauchy completeness and Heine–Borel, and it is the usual
--   route to the extreme value theorem. Properness is essential: in an infinite-dimensional
--   Hilbert space the orthonormal sequence $e_n$ is bounded with no convergent subsequence.
--
--   Bolzano proved it in 1817 in the course of giving an analytic proof of the intermediate value
--   theorem; Weierstrass rediscovered it decades later.
--
--   **Formalization note.** `ProperSpace X` says closed balls are compact; `Bornology.IsBounded`
--   is metric boundedness and `StrictMono φ` extracts a genuine subsequence. The result is
--   Mathlib's `tendsto_subseq_of_bounded`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests (docs/undergrad.yaml, docs/overview.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

open Filter Set Topology DirectSum

theorem bolzano_weierstrass {X : Type*} [PseudoMetricSpace X] [ProperSpace X] {s : Set X}
    (hs : Bornology.IsBounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by sorry

end FamousTheorems
