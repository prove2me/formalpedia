-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_B_5
-- name    : ElimAgree.Supplement.theorem_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:42:42.471195+00:00
-- url     : https://prove2.me/theorems/328eacd1-4e0b-4bf5-b039-8b32c185b698
-- title:
--   Theorem B.5 (Sharp randomized bound) for $\mathrm{REIP}_{n,k}$
-- statement:
--   For $1\le k\le n$ and $0<g\le1$,
--
--   $$R^{\mathrm{pub},A}_{(1-g)2^{-k}}(\mathrm{REIP}_{n,k})\ \ge\ \log(2^n-1)-k-\log k+2\log g-19,$$
--
--   where the lower bound allows interaction and either output party at each leaf. For fixed $0<\alpha<1$ there is $C(\alpha)$ such that for all $n,k\ge1$
--
--   $$\Big|R^{\mathrm{pub},A}_{\alpha2^{-k}}(\mathrm{REIP}_{n,k})-\max\{n-k-\log k,0\}\Big|\le C(\alpha),$$
--
--   and the matching upper bound is achieved by a deterministic one-way protocol (Bob sends, Alice outputs, never wrong). In particular, for $1\le k\le n$, deterministic interactive protocols that never err need $\log(2^n-1)-k-\log k-19$ bits.
--
--   **Formalization Note** Lower bounds are for every protocol with the output party designated at each leaf; the deterministic statements are about single trees.
--
--   Differences from the source:
--   - encoding: a lower bound on R_ϵ (least worst-case cost) → every protocol of cost c (all trees in its support of depth ≤ c) with pointwise error ≤ ϵ has c ≥ the bound; reason: R is the least such cost, so the two say the same; avoids sInf of a possibly empty set
--   - generalization: "for fixed 0 < α < 1, R = max{n − k − log k, 0} + O_α(1)" (in a sentence starting "For 1 ≤ k ≤ n") → for all n, k ≥ 1, with C(α) chosen before n, k; reason: restricted to 1 ≤ k ≤ n it is the source's claim with the same C(α); for k > n it also holds (max{…} = 0, and M*(n, k) = 1 by Theorem B.1 gives a depth-0 tree)
--   - reading: the matching upper bound is deterministic and one-way → one tree with only Bob nodes, Alice output, never erring, depth ≤ max{…} + C; reason: a deterministic protocol with error below 1 never errs
--   - reading: deterministic interactive protocols need log(2^n − 1) − k − log k − 19 bits → every single tree with designated output party that never errs has depth ≥ that; reason: the proof: a deterministic protocol that never errs has g = 1
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem B.5, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_Models
import Definitions.Def_ElimAgree_Supplement_REIP

namespace ElimAgree

namespace Supplement

/-- Theorem B.5 (Sharp randomized bound), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.33. For `1 ≤ k ≤ n` and `0 < g ≤ 1`,
`R^{pub,A}_{(1−g)2^{−k}}(REIP_{n,k}) ≥ log(2^n − 1) − k − log k + 2 log g − 19`, and for fixed `0 < α < 1`,
`R^{pub,A}_{α2^{−k}}(REIP_{n,k}) = max{n − k − log k, 0} + O_α(1)`. The lower bound allows interaction and
either output party at each leaf; the matching upper bound is deterministic and one-way. In
particular, deterministic interactive protocols need `log(2^n − 1) − k − log k − 19` bits.

**Formalization Note.** Alice holds `X`, Bob holds `y`, and a run fails iff the output equals `Xy`.
Lower bounds are for every public-coin protocol with the output party designated at each leaf (base
`desErr`) of cost `c`. `O_α(1)` is a constant `C(α)` chosen before `n`, `k`; the upper bound is one
deterministic tree with only Bob's nodes, of depth at most `max{n − k − log k, 0} + C`, whose leaves
carry Alice's output and which never errs. The `O_α(1)` clause is stated for all `n, k ≥ 1`. A
deterministic protocol is a single tree; "need" is a lower bound on its depth when it never errs. -/
theorem theorem_B_5 :
    (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ g : ℝ, 0 < g → g ≤ 1 →
      ∀ (c : ℕ) (μ : PMF (DesProt (Mat k n) (Vec n) (Fin k → ZMod 2))), CostLE μ c →
      (∀ X y, desErr reipAns μ X y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) →
      Real.logb 2 ((2 : ℝ) ^ n - 1) - k - Real.logb 2 k + 2 * Real.logb 2 g - 19 ≤ (c : ℝ)) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      (∀ (c : ℕ) (μ : PMF (DesProt (Mat k n) (Vec n) (Fin k → ZMod 2))), CostLE μ c →
        (∀ X y, desErr reipAns μ X y ≤ ENNReal.ofReal (α / 2 ^ k)) →
        max ((n : ℝ) - k - Real.logb 2 k) 0 - C ≤ (c : ℝ)) ∧
      ∃ T : AliceProt (Mat k n) (Vec n) (Fin k → ZMod 2), IsOneWayBA T ∧
        (T.depth : ℝ) ≤ max ((n : ℝ) - k - Real.logb 2 k) 0 + C ∧
        ∀ X y, T.eval X y X ≠ reipAns X y) ∧
    (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ T : DesProt (Mat k n) (Vec n) (Fin k → ZMod 2),
      (∀ X y, ¬ desFails (T.eval X y) X y (reipAns X y)) →
      Real.logb 2 ((2 : ℝ) ^ n - 1) - k - Real.logb 2 k - 19 ≤ (T.depth : ℝ)) := by sorry

end Supplement

end ElimAgree
