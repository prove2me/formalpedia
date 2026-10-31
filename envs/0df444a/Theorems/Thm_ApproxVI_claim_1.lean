-- Prove2me | Theorems.Thm_ApproxVI_claim_1
-- name    : ApproxVI.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:16:09.293218+00:00
-- url     : https://prove2.me/theorems/af5df1e0-d756-4e50-896c-fc03bfd54bad
-- title:
--   Claim 1 and (10) — the weighted Hausdorff distance between $\tilde Tx$ and $\tilde Ty$
-- statement:
--   Let $\nu$ be positive weights, $\epsilon>0$, $T:\mathbb R^d\to\mathbb R^d$ and $\tilde Tx=Tx+B^\epsilon$. For all $x,y\in\mathbb R^d$:
--
--   1. there exist $x^*\in\tilde Tx$ and $y^*\in\tilde Ty$ such that $\|x^*-y^*\|_\nu=H_\nu(\tilde Tx,\tilde Ty)$;
--   2. for any $x_0\in\tilde Tx$ and $y_0\in\tilde Ty$,
--
--   $$
--   \|x_0-y_0\|_\nu\le2\epsilon+H_\nu(\tilde Tx,\tilde Ty).\qquad(10)
--   $$
--
--   Inequality (10) is the step that turns the AVI coupling estimate into (13).
--
--   **Formalization Note** $H_\nu$ takes values in $[0,\infty]$; real norms are embedded as nonnegative extended reals.
--
--   Differences from the source:
--   - generalization: T the Bellman operator (3) under (AV1)–(AV5) → T any map ℝ^d → ℝ^d; reason: T̃x and T̃y are translates of the same ball B^ε, so neither part uses a property of T; the source's T is an instance
--   - encoding: H_ν real-valued → H_ν in [0, ∞], norms embedded by ENNReal.ofReal; reason: all quantities are nonnegative and here finite; no instance changes
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, Claim 1 and (10), p.15

import Mathlib
import Definitions.Def_ApproxVI_Ttilde
import Definitions.Def_ApproxVI_hausNu

namespace ApproxVI

open scoped ENNReal

/-- **Claim 1 and (10)**, Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration
Algorithms*, arXiv:1709.04673v5, p.15: given `x, y ∈ ℝ^d`,
(a) there exist `x* ∈ T̃x` and `y* ∈ T̃y` such that `‖x* − y*‖_ν = H_ν(T̃x, T̃y)`; and
(b) for any `x₀ ∈ T̃x` and `y₀ ∈ T̃y`, `‖x₀ − y₀‖_ν ≤ 2ε + H_ν(T̃x, T̃y)` (10).

**Formalization Note** `H_ν` takes values in `ℝ≥0∞` (`hausNu`); the real norms are embedded
with `ENNReal.ofReal`, which is exact on nonnegative reals. `T` is any map: both `T̃x` and
`T̃y` are `‖·‖_ν`-balls of radius `ε`, and neither part uses (AV1). -/
theorem claim_1 {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i)
    (T : (Fin d → ℝ) → (Fin d → ℝ)) (ε : ℝ) (hε : 0 < ε) (x y : Fin d → ℝ) :
    (∃ xs ∈ Ttilde ν T ε x, ∃ ys ∈ Ttilde ν T ε y,
        ENNReal.ofReal (wNorm ν (xs - ys)) = hausNu ν (Ttilde ν T ε x) (Ttilde ν T ε y)) ∧
      ∀ x₀ ∈ Ttilde ν T ε x, ∀ y₀ ∈ Ttilde ν T ε y,
        ENNReal.ofReal (wNorm ν (x₀ - y₀)) ≤
          ENNReal.ofReal (2 * ε) + hausNu ν (Ttilde ν T ε x) (Ttilde ν T ε y) := by sorry

end ApproxVI
