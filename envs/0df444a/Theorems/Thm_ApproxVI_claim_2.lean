-- Prove2me | Theorems.Thm_ApproxVI_claim_2
-- name    : ApproxVI.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:13.545244+00:00
-- url     : https://prove2.me/theorems/c0cf58c8-a668-480b-8afe-3fea63f870cd
-- title:
--   Claim 2, (11) — comparison of $\|\cdot\|_\nu$, $\|\cdot\|_\infty$ and the Euclidean norm
-- statement:
--   Let $d\ge1$, let $\nu$ be a vector of positive weights, and put $\nu_{\max}=\max_i\nu_i$, $\nu_{\min}=\min_i\nu_i$. For every $z\in\mathbb R^d$,
--
--   $$
--   \nu_{\min}\|z\|_\nu\le\|z\|_\infty\le\|z\|\le\big(\sqrt d\,\nu_{\max}\big)\|z\|_\nu,
--   $$
--
--   where $\|z\|_\infty=\max_i|z_i|$ and $\|z\|$ is the Euclidean norm.
--
--   These comparisons transfer bounds between the weighted max-norm of (AV1) and the Euclidean norm of (AV5) and of the stability statement.
--
--   **Formalization Note** $\|z\|_\infty$ is Mathlib's norm on `Fin d → ℝ`; $d\ge1$ is an instance argument.
--
--   Differences from the source:
--   - encoding: ‖z‖_∞, the Euclidean ‖z‖, ν_max, ν_min with d ≥ 1 → Mathlib's sup norm ‖z‖ on Fin d → ℝ, euclNorm z = √(Σ z_i²), Finset.univ.sup' / inf' of ν with d ≥ 1 as [NeZero d]; reason: Lean forms of the same quantities; Mathlib's norm on Fin d → ℝ is the sup norm, so the Euclidean norm is explicit; no instance changes
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, Claim 2, (11), p.15 (ν_max, ν_min defined on p.14)

import Mathlib
import Definitions.Def_ApproxVI_wNorm
import Definitions.Def_ApproxVI_euclNorm

namespace ApproxVI

/-- **Claim 2, (11)**, Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration
Algorithms*, arXiv:1709.04673v5, p.15: for any `z ∈ ℝ^d`,
`ν_min ‖z‖_ν ≤ ‖z‖_∞ ≤ ‖z‖ ≤ (√d ν_max) ‖z‖_ν`,
with `ν_max := max {νᵢ}` and `ν_min := min {νᵢ}` (p.14).

**Formalization Note** `‖z‖_∞` is Mathlib's norm `‖z‖` on `Fin d → ℝ` (the sup norm);
`‖z‖` of the page is the Euclidean norm `euclNorm z`. `d ≥ 1` (p.14) is `[NeZero d]`, which
makes `ν_max`, `ν_min` (`Finset.sup'`, `Finset.inf'` over all indices) defined. -/
theorem claim_2 {d : ℕ} [NeZero d] (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (z : Fin d → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty ν * wNorm ν z ≤ ‖z‖ ∧
      ‖z‖ ≤ euclNorm z ∧
      euclNorm z ≤ Real.sqrt d * Finset.univ.sup' Finset.univ_nonempty ν * wNorm ν z := by sorry

end ApproxVI
