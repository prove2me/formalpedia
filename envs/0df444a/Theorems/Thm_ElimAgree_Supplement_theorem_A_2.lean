-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_A_2
-- name    : ElimAgree.Supplement.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:41:00.488803+00:00
-- url     : https://prove2.me/theorems/b9676801-b4a2-48f2-8527-5cf2a3daf0aa
-- title:
--   Theorem A.2 (Random functions) — both complexities up to $\pm O(1)$ with probability $1-e^{-\Omega(2^n)}$
-- statement:
--   Let $f:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}$ be uniformly random. There are absolute constants $c_0>0$ and $C$ such that for every $n\ge1$, with probability at least $1-e^{-c_0 2^n}$, simultaneously for all $k\ge1$:
--
--   1. for $0<g\le\tfrac12$, $\ R^{\mathrm{pub},A}_{(1-g)2^{-k}}\big(\mathrm{Elim}(f^k)\big)=[n-\log k+2\log g]_+\pm C$;
--   2. for $0<g\le1$, $\ R^{\mathrm{pub,com}}_{(1-g)2^{-k}}\big(\mathrm{Elim}(f^k)\big)=[n+2\log g]_+\pm C$.
--
--   The local-output lower bound allows the output party to be designated at each leaf.
--
--   $$\Pr_f\big[\text{1 and 2 hold for all }k\ge1\big]\ \ge\ 1-e^{-c_0 2^n}.$$
--
--   So for almost every function both complexities are determined up to an additive constant, uniformly in $k$ and $g$.
--
--   **Formalization Note** The probability is the fraction of the $2^{2^{2n}}$ functions in the event. In item 1 the lower bound is for every designated-output protocol and the upper bound is by an Alice-output protocol; in item 2 both are for common output.
--
--   Differences from the source:
--   - reading: with probability 1 − e^{−Ω(2^n)}, with absolute constants → ∃ c₀ > 0 and C, chosen before n: for every n ≥ 1 the event has probability ≥ 1 − e^{−c₀2^n}; reason: Ω and O(1) are absolute constants; the proof covers n ≤ 12 by a large constant
--   - reading: R^{pub,A} = [·]_+ ± O(1), the lower bound allowing a designated output party → every designated-output protocol costs ≥ [·]_+ − C, some Alice-output protocol costs ≤ [·]_+ + C; reason: R^{pub,A} is Alice output (Definition 2.1); the designated class contains it, so both complexities lie within C
--   - encoding: uniformly random f → counting fraction over all 2^{2^{2n}} functions; reason: same probability
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem A.2, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_Models

namespace ElimAgree

namespace Supplement

/-- Theorem A.2 (Random functions), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.29. Let `f : {0, 1}^n × {0, 1}^n → {0, 1}` be uniformly random.
With probability `1 − e^{−Ω(2^n)}`, simultaneously for all `k ≥ 1`,
`R^{pub,A}_{(1−g)2^{−k}}(Elim(f^k)) = [n − log k + 2 log g]_+ ± O(1)` (`0 < g ≤ 1/2`) and
`R^{pub,com}_{(1−g)2^{−k}}(Elim(f^k)) = [n + 2 log g]_+ ± O(1)` (`0 < g ≤ 1`), with absolute constants.
The local-output lower bound allows the output party to be designated at each leaf.

**Formalization Note.** The probability is the fraction of the `2^{2^{2n}}` functions in the event.
The constants are pinned: there are `c₀ > 0` and `C` such that for every `n ≥ 1` the event below has
probability at least `1 − e^{−c₀ 2^n}`. The event serves all `k ≥ 1` and all `g` at once. In it, every
designated-output protocol (base `desErr`) with pointwise error at most `(1 − g)2^{−k}` costs at least
`[n − log k + 2 log g]_+ − C` and some Alice-output protocol with that error costs at most
`[n − log k + 2 log g]_+ + C` (`0 < g ≤ 1/2`); every common-output protocol (base `comErr`) with that
error costs at least `[n + 2 log g]_+ − C` and one costs at most `[n + 2 log g]_+ + C` (`0 < g ≤ 1`). -/
theorem theorem_A_2 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      1 - Real.exp (-(c₀ * 2 ^ n)) ≤
        (({f : (Fin n → Bool) → (Fin n → Bool) → Bool |
          ∀ k : ℕ, 1 ≤ k →
            (∀ g : ℝ, 0 < g → g ≤ 1 / 2 →
              (∀ (c : ℕ)
                (μ : PMF (DesProt (Fin k → Fin n → Bool) (Fin k → Fin n → Bool) (Fin k → Bool))),
                CostLE μ c →
                (∀ x y, desErr (elimAns (X := fun _ => Fin n → Bool) (Y := fun _ => Fin n → Bool)
                  (fun _ : Fin k => f)) μ x y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) →
                max ((n : ℝ) - Real.logb 2 k + 2 * Real.logb 2 g) 0 - C ≤ (c : ℝ)) ∧
              ∃ (c : ℕ)
                (μ : PMF (AliceProt (Fin k → Fin n → Bool) (Fin k → Fin n → Bool) (Fin k → Bool))),
                CostLE μ c ∧
                (∀ x y, aliceErr (elimAns (X := fun _ => Fin n → Bool) (Y := fun _ => Fin n → Bool)
                  (fun _ : Fin k => f)) μ x y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) ∧
                (c : ℝ) ≤ max ((n : ℝ) - Real.logb 2 k + 2 * Real.logb 2 g) 0 + C) ∧
            (∀ g : ℝ, 0 < g → g ≤ 1 →
              (∀ (c : ℕ)
                (μ : PMF (ComProtG (Fin k → Fin n → Bool) (Fin k → Fin n → Bool) (Fin k → Bool))),
                CostLE μ c →
                (∀ x y, comErr (elimAns (X := fun _ => Fin n → Bool) (Y := fun _ => Fin n → Bool)
                  (fun _ : Fin k => f)) μ x y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) →
                max ((n : ℝ) + 2 * Real.logb 2 g) 0 - C ≤ (c : ℝ)) ∧
              ∃ (c : ℕ)
                (μ : PMF (ComProtG (Fin k → Fin n → Bool) (Fin k → Fin n → Bool) (Fin k → Bool))),
                CostLE μ c ∧
                (∀ x y, comErr (elimAns (X := fun _ => Fin n → Bool) (Y := fun _ => Fin n → Bool)
                  (fun _ : Fin k => f)) μ x y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) ∧
                (c : ℝ) ≤ max ((n : ℝ) + 2 * Real.logb 2 g) 0 + C)} :
          Set ((Fin n → Bool) → (Fin n → Bool) → Bool)).ncard : ℝ) / 2 ^ (2 ^ (2 * n)) := by sorry

end Supplement

end ElimAgree
