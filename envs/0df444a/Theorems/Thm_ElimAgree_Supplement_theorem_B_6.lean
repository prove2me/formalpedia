-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_B_6
-- name    : ElimAgree.Supplement.theorem_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:43:17.315221+00:00
-- url     : https://prove2.me/theorems/46c31bc3-96ff-47d7-84e4-e2e0ac72c2e4
-- title:
--   Theorem B.6 (Common-output restricted inner product) — $\max\{n-k,0\}+O_\alpha(1)$
-- statement:
--   For $1\le k\le n$ and every $0\le\epsilon<2^{-k}$,
--
--   $$R^{\mathrm{pub,com}}_\epsilon(\mathrm{REIP}_{n,k})\ \ge\ n-k+2\log(1-2^k\epsilon),$$
--
--   and for all $n,k\ge1$ and $0<\alpha<1$,
--
--   $$R^{\mathrm{pub,com}}_{\alpha2^{-k}}(\mathrm{REIP}_{n,k})\ \le\ \max\{n-k+1,0\}+\big\lceil\log\big(\lceil\log(1/\alpha)\rceil+1\big)\big\rceil,$$
--
--   by a protocol that uses one message from Bob followed by one message from Alice. Hence for fixed $\alpha$, $R^{\mathrm{pub,com}}_{\alpha2^{-k}}(\mathrm{REIP}_{n,k})=\max\{n-k,0\}+O_\alpha(1)$. The lower bound allows the parties to disagree on failed runs.
--
--   **Formalization Note** $\max\{n-k+1,0\}$ is natural-number subtraction $n+1-k$. "One message from Bob followed by one from Alice" means that on every path of every tree Bob's nodes come first.
--
--   Differences from the source:
--   - reading: ϵ < 2^{−k} (an error probability) → 0 ≤ ϵ < 2^{−k}; reason: for ϵ < 0 the constraint, read in [0,∞], would mean zero error while the bound grows; the source only means probabilities
--   - encoding: a lower bound on R_ϵ (least worst-case cost) → every protocol of cost c (all trees in its support of depth ≤ c) with pointwise error ≤ ϵ has c ≥ the bound; reason: R is the least such cost, so the two say the same; avoids sInf of a possibly empty set
--   - reading: = max{n − k, 0} + O_α(1) → ∃ C(α) chosen before n, k: every protocol with error ≤ α2^{−k} costs ≥ max{n − k, 0} − C, one costs ≤ max{n − k, 0} + C; reason: R is the least cost
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem B.6, pp.33–34 (PDF pp.35–36)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_Models
import Definitions.Def_ElimAgree_Supplement_REIP

namespace ElimAgree

namespace Supplement

/-- Theorem B.6 (Common-output restricted inner product), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), pp.33–34. For `1 ≤ k ≤ n` and every
`ϵ < 2^{−k}`, `R^{pub,com}_ϵ(REIP_{n,k}) ≥ n − k + 2 log(1 − 2^kϵ)`, and for all `n, k ≥ 1` and
`0 < α < 1`, `R^{pub,com}_{α2^{−k}}(REIP_{n,k}) ≤ max{n − k + 1, 0} + ⌈log(⌈log(1/α)⌉ + 1)⌉`. Hence
`R^{pub,com}_{α2^{−k}}(REIP_{n,k}) = max{n − k, 0} + O_α(1)`. The lower bound allows the parties to
disagree on failed runs; the upper bound uses one message from Bob followed by one message from
Alice.

**Formalization Note.** Common output is the base `ComLabel`/`comErr` (a run fails if the outputs
differ or both equal `Xy`). `max{n − k + 1, 0}` is the natural-number subtraction `n + 1 − k`. The
upper-bound protocol is a `PMF` over trees in which, on every path, Bob's nodes precede Alice's
(`IsBobThenAlice`). `ϵ ≥ 0` is an error probability. `O_α(1)` is a constant `C(α)` chosen before
`n, k`. -/
theorem theorem_B_6 :
    (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 ^ k →
      ∀ (c : ℕ) (μ : PMF (ComProtG (Mat k n) (Vec n) (Fin k → ZMod 2))), CostLE μ c →
      (∀ X y, comErr reipAns μ X y ≤ ENNReal.ofReal ε) →
      (n : ℝ) - k + 2 * Real.logb 2 (1 - 2 ^ k * ε) ≤ (c : ℝ)) ∧
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∀ α : ℝ, 0 < α → α < 1 →
      ∃ μ : PMF (ComProtG (Mat k n) (Vec n) (Fin k → ZMod 2)),
        (∀ T ∈ μ.support, IsBobThenAlice T) ∧
        CostLE μ (n + 1 - k + ⌈Real.logb 2 ((⌈Real.logb 2 (1 / α)⌉₊ : ℝ) + 1)⌉₊) ∧
        ∀ X y, comErr reipAns μ X y ≤ ENNReal.ofReal (α / 2 ^ k)) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      (∀ (c : ℕ) (μ : PMF (ComProtG (Mat k n) (Vec n) (Fin k → ZMod 2))), CostLE μ c →
        (∀ X y, comErr reipAns μ X y ≤ ENNReal.ofReal (α / 2 ^ k)) →
        max ((n : ℝ) - k) 0 - C ≤ (c : ℝ)) ∧
      ∃ (c : ℕ) (μ : PMF (ComProtG (Mat k n) (Vec n) (Fin k → ZMod 2))), CostLE μ c ∧
        (∀ X y, comErr reipAns μ X y ≤ ENNReal.ofReal (α / 2 ^ k)) ∧
        (c : ℝ) ≤ max ((n : ℝ) - k) 0 + C) := by sorry

end Supplement

end ElimAgree
