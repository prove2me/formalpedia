-- Prove2me | Theorems.Thm_EReal_coe_finset_sum
-- name    : EReal.coe_finset_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:37.142752+00:00
-- url     : https://prove2.me/theorems/5280979f-5321-4cac-a93d-2fa3a6e18698
-- title:
--   The coercion `ℝ → EReal` commutes with finite sums
-- statement:
--   Let $\overline{\mathbb{R}} = [-\infty, +\infty]$ be the extended reals and write
--   $\iota : \mathbb{R} \to \overline{\mathbb{R}}$ for the canonical inclusion. For a finite index
--   set $s$ and any family $f : \iota \to \mathbb{R}$,
--
--   $$
--   \iota\Bigl(\sum_{i \in s} f(i)\Bigr) \;=\; \sum_{i \in s} \iota\bigl(f(i)\bigr).
--   $$
--
--   The inclusion of the reals into the extended reals commutes with finite sums. This is routine
--   but unavoidable: addition on $\overline{\mathbb{R}}$ is not a group operation, so no general
--   algebraic lemma applies, and any argument that computes with a finite sum of real quantities
--   inside an $\overline{\mathbb{R}}$-valued expression — as convex analysis with
--   $+\infty$-valued functions constantly does — needs exactly this step.
--
--   **Formalization Note** $\overline{\mathbb{R}}$ is `EReal`, $s$ is a `Finset`, and the sums are
--   `Finset.sum` on each side.
-- source:
--   Elementary property of the order-embedding $\mathbb{R} \hookrightarrow \overline{\mathbb{R}}$; carved from the accepted proof of EmpiricalDRO.Discrete.proposition1_discrete_reduction, https://prove2.me/submissions/28498841-88d3-4588-8338-6c8af1fdca7b

import Mathlib

open Finset

theorem EReal.coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by sorry
