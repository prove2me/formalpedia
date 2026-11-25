-- Prove2me | Theorems.Thm_ErdosDyadic_periodic_hitting
-- name    : ErdosDyadic.periodic_hitting
-- status  : Open
-- author  : @Jhon Lenin Acuna
-- created : 2026-11-25T04:22:20.254166+00:00
-- url     : https://prove2.me/theorems/0f1909f4-4fcc-5cd0-a223-1b8faf383c15
-- title:
--   Periodic hitting sets (Lemma 2.1)
-- statement:
--   **Lemma 2.1 (periodic hitting sets).** For every $p\in(0,1)$ there is an open 1-periodic set $H\subseteq\mathbb R$ with $\rho(H)\le 6p$ such that
--   $$\forall x\in\mathbb R\ \ \forall t\in[1,2]\ \ \exists n\in\mathbb Z_{\ge1}:\quad x+t\,2^{-n}\in H .$$
--
--   The same $H$ serves every center $x$ and every scale $t\in[1,2]$; only the witness $n$ depends on them. This is the technical heart of the paper: a small-density open periodic set meeting every copy $x+tD$ with normalized scale $t\in[1,2]$.
--
--   **Formalization Note** $\rho(H)\le 6p$ is stated in $[0,\infty]$ via `ENNReal.ofReal`.
-- source:
--   OpenAI, The dyadic case of the Erdős similarity conjecture, Sept 25, 2026, https://github.com/openai/math/tree/main/preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026, Lemma 2.1, p. 4 (proved in Sections 3-5)

import Mathlib
import Definitions.Def_erdos_dyadic_IsPeriodic1
import Definitions.Def_erdos_dyadic_rho

open MeasureTheory Set

namespace ErdosDyadic

/-- Lemma 2.1: periodic hitting sets. -/
theorem periodic_hitting (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ H : Set ℝ, IsOpen H ∧ IsPeriodic1 H ∧ rho H ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x : ℝ, ∀ t ∈ Icc (1 : ℝ) 2, ∃ n : ℕ, 1 ≤ n ∧ x + t * (2 : ℝ) ^ (-(n : ℤ)) ∈ H := by
  sorry

end ErdosDyadic
