-- Prove2me | Theorems.Thm_ApproxVI_lemma_1
-- name    : ApproxVI.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:15:10.15899+00:00
-- url     : https://prove2.me/theorems/5e370337-2f4f-4089-bbf7-6ae73eb17dd5
-- title:
--   Lemma 1 — the weighted ball $B^\epsilon$ is convex and compact
-- statement:
--   Let $\nu$ be a vector of positive weights and $\epsilon>0$. Then
--
--   $$
--   B^\epsilon=\{y\in\mathbb R^d:\ \|y\|_\nu\le\epsilon\}
--   $$
--
--   is a convex compact subset of $\mathbb R^d$.
--
--   This gives property (i) of a Marchaud map for the perturbed Bellman operator $\tilde Tx=Tx+B^\epsilon$ (Lemma 2).
--
--   Differences from the source: none.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, Lemma 1, p.14

import Mathlib
import Definitions.Def_ApproxVI_ballNu

namespace ApproxVI

/-- **Lemma 1**, Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration Algorithms*,
arXiv:1709.04673v5, p.14: `B^ε := {y | ‖y‖_ν ≤ ε}` is a convex compact subset of `ℝ^d`,
where `ε > 0`.

**Formalization Note** `ℝ^d` is `Fin d → ℝ` with its product (= norm) topology; the weights
satisfy `νᵢ > 0` (§3.1, p.7). -/
theorem lemma_1 {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (ε : ℝ) (hε : 0 < ε) :
    Convex ℝ (ballNu ν ε) ∧ IsCompact (ballNu ν ε) := by sorry

end ApproxVI
