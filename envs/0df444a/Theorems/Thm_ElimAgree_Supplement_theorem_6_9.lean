-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_6_9
-- name    : ElimAgree.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:40:04.287893+00:00
-- url     : https://prove2.me/theorems/ec954105-93ad-43e3-959f-a17e8604b37c
-- title:
--   Theorem 6.9 (Common-output inner product) — $[n+2\log g]_++O(1)$ for every $k$
-- statement:
--   For $n\ge2$, every $k\ge1$ and every $0\le\epsilon<2^{-k}$,
--
--   $$R^{\mathrm{pub,com}}_\epsilon\big(\mathrm{Elim}(\mathrm{IP}_n^k)\big)\ \ge\ n-2+2\log(1-2^k\epsilon).$$
--
--   Consequently there is an absolute constant $C$ such that for all $n\ge2$, every $0<g\le1$ and every $k\ge1$,
--
--   $$\Big|R^{\mathrm{pub,com}}_{(1-g)2^{-k}}\big(\mathrm{Elim}(\mathrm{IP}_n^k)\big)-[n+2\log g]_+\Big|\le C.$$
--
--   The bound is uniform in $k$ and $g$, with additive loss two in the first display.
--
--   **Formalization Note** The two-sided statement is: every protocol with that error costs at least $[n+2\log g]_+-C$, and one costs at most $[n+2\log g]_++C$.
--
--   Differences from the source:
--   - reading: ϵ < 2^{−k} (an error probability) → 0 ≤ ϵ < 2^{−k}; reason: for ϵ < 0 the constraint, read in [0,∞], would mean zero error while the bound grows; the source only means probabilities
--   - encoding: a lower bound on R_ϵ (least worst-case cost) → every protocol of cost c (all trees in its support of depth ≤ c) with pointwise error ≤ ϵ has c ≥ the bound; reason: R is the least such cost, so the two say the same; avoids sInf of a possibly empty set
--   - reading: = [n + 2 log g]_+ + O(1) for every 0 < g ≤ 1 and every k → ∃ absolute C chosen before n, k, g; lower bound for every protocol, upper bound by one protocol; n ≥ 2 as in the first sentence; reason: R is the least cost; O(1) is an absolute constant
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 6.9, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_Models
import Definitions.Def_ElimAgree_Supplement_SignOp

namespace ElimAgree

namespace Supplement

/-- Theorem 6.9 (Common-output inner product), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.25. For `n ≥ 2`, every `k ≥ 1` and every
`ϵ < 2^{−k}`, `R^{pub,com}_ϵ(Elim(IP_n^k)) ≥ n − 2 + 2 log(1 − 2^kϵ)`. Consequently, for every
`0 < g ≤ 1` and with no restriction on `k`, `R^{pub,com}_{(1−g)2^{−k}}(Elim(IP_n^k)) = [n + 2 log g]_+ + O(1)`.

**Formalization Note.** `IP_n` is `ipFun n` on `Fin n → Bool`. The lower bound is stated for every
common-output protocol (base `comErr`) of cost `c` with pointwise error at most `ϵ ≥ 0`. `O(1)` is an
absolute constant `C` chosen before `n`, `k` and `g`: every protocol with error at most
`(1 − g)2^{−k}` costs at least `[n + 2 log g]_+ − C`, and one costs at most `[n + 2 log g]_+ + C`. -/
theorem theorem_6_9 :
    (∀ n k : ℕ, 2 ≤ n → 1 ≤ k → ∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 ^ k →
      ∀ (c : ℕ) (μ : PMF (ComProtG (Fin k → Fin n → Bool) (Fin k → Fin n → Bool) (Fin k → Bool))),
      CostLE μ c →
      (∀ x y, comErr (elimAns (X := fun _ => Fin n → Bool) (Y := fun _ => Fin n → Bool)
        (fun _ : Fin k => ipFun n)) μ x y ≤ ENNReal.ofReal ε) →
      (n : ℝ) - 2 + 2 * Real.logb 2 (1 - 2 ^ k * ε) ≤ (c : ℝ)) ∧
    (∃ C : ℝ, ∀ n k : ℕ, 2 ≤ n → 1 ≤ k → ∀ g : ℝ, 0 < g → g ≤ 1 →
      (∀ (c : ℕ)
        (μ : PMF (ComProtG (Fin k → Fin n → Bool) (Fin k → Fin n → Bool) (Fin k → Bool))),
        CostLE μ c →
        (∀ x y, comErr (elimAns (X := fun _ => Fin n → Bool) (Y := fun _ => Fin n → Bool)
          (fun _ : Fin k => ipFun n)) μ x y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) →
        max ((n : ℝ) + 2 * Real.logb 2 g) 0 - C ≤ (c : ℝ)) ∧
      ∃ (c : ℕ)
        (μ : PMF (ComProtG (Fin k → Fin n → Bool) (Fin k → Fin n → Bool) (Fin k → Bool))),
        CostLE μ c ∧
        (∀ x y, comErr (elimAns (X := fun _ => Fin n → Bool) (Y := fun _ => Fin n → Bool)
          (fun _ : Fin k => ipFun n)) μ x y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) ∧
        (c : ℝ) ≤ max ((n : ℝ) + 2 * Real.logb 2 g) 0 + C) := by sorry

end Supplement

end ElimAgree
