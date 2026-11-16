-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_3_21
-- name    : ElimAgree.Supplement.theorem_3_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:38:26.752118+00:00
-- url     : https://prove2.me/theorems/f980ea93-3d35-49f5-82e1-739ab1ef57ce
-- title:
--   Theorem 3.21 (One-way local output) — $\Theta_\alpha(\min\{n,1+n^2/k\})$ for disjointness
-- statement:
--   Let $n\ge7$, $k\ge1$ and $\ell=\lfloor(n+1)/4\rfloor$. If a public-coin protocol for $\mathrm{Elim}(\mathrm{DISJ}_n^k)$ in which Bob sends at most $c$ bits and Alice outputs has error at most $(1-g)2^{-k}$ on every input, then, with $t=c\ln2+1+\ln2$,
--
--   $$g\ \le\ \frac{32\sqrt{2e}}{\ell}\sqrt{kt}+\frac{16}{\ell}\,t.$$
--
--   Consequently, for every fixed $0<\alpha<1$ there are $C_1(\alpha),C_2(\alpha)>0$ such that for all $n,k\ge1$
--
--   $$C_1\min\Big\{n,1+\frac{n^2}k\Big\}\ \le\ R^{\mathrm{pub},B\to A}_{\alpha2^{-k}}\big(\mathrm{Elim}(\mathrm{DISJ}_n^k)\big)\ \le\ C_2\min\Big\{n,1+\frac{n^2}k\Big\}.$$
--
--   This settles one-way local-output elimination of disjointness at every $k$.
--
--   **Formalization Note** Bob's message is the path of a tree in which only Bob speaks; inputs and answers are the base mission's `Inp`, `disjAns`, and $\ell$ is the base `ell`. The complexity statement is: every such protocol with error at most $\alpha2^{-k}$ costs at least $C_1\min\{\cdot\}$, and one costs at most $C_2\min\{\cdot\}$.
--
--   Differences from the source:
--   - reading: first claim, k unspecified → 1 ≤ k; reason: k is the number of instances
--   - encoding: Bob sends at most c bits and Alice outputs → trees with only Bob nodes, depth ≤ c, Alice's output at the leaves; reason: Bob's message is the root-to-leaf path
--   - reading: R = Θ_α(min{n, 1 + n²/k}) for fixed α and all n, k ≥ 1 → ∃ C₁, C₂ > 0 depending only on α, chosen before n and k: every protocol with error ≤ α2^{−k} costs ≥ C₁·min, and some protocol costs ≤ C₂·min; reason: R is the least cost; this is Θ_α
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 3.21, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ElimAgree_nuDisj
import Definitions.Def_ElimAgree_Supplement_Models

namespace ElimAgree

namespace Supplement

/-- Theorem 3.21 (One-way local output), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.16. Let `n ≥ 7` and `ℓ = ⌊(n + 1)/4⌋`. If a public-coin
protocol in which Bob sends at most `c` bits and Alice outputs has error at most `(1 − g)2^{−k}`,
then, with `t = c ln 2 + 1 + ln 2`, `g ≤ (32√(2e)/ℓ)√(kt) + (16/ℓ)t`. Consequently, for fixed
`0 < α < 1` and all `n, k ≥ 1`, `R^{pub,B→A}_{α2^{−k}}(Elim(DISJ_n^k)) = Θ_α(min{n, 1 + n²/k})`.

**Formalization Note.** Inputs are the base `Inp n k` with answer `disjAns`; `ℓ` is the base
`ell n`. "Bob sends at most `c` bits and Alice outputs" is a `PMF` over trees with only Bob's nodes
(`IsOneWayBA`) and depth at most `c` (`CostLE`), whose leaves carry Alice's output. Error is
pointwise. `Θ_α` is pinned as constants `C₁(α), C₂(α) > 0` chosen before `n` and `k`: every such
protocol with error at most `α2^{−k}` costs at least `C₁ min{n, 1 + n²/k}`, and one costs at most
`C₂ min{n, 1 + n²/k}`. -/
theorem theorem_3_21 :
    (∀ n k : ℕ, 7 ≤ n → 1 ≤ k → ∀ (g : ℝ) (c : ℕ)
      (μ : PMF (AliceProt (Inp n k) (Inp n k) (Fin k → Bool))),
      (∀ T ∈ μ.support, IsOneWayBA T) → CostLE μ c →
      (∀ X Y : Inp n k, aliceErr disjAns μ X Y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) →
      g ≤ 32 * Real.sqrt (2 * Real.exp 1) / (ell n : ℝ) *
          Real.sqrt (k * (c * Real.log 2 + 1 + Real.log 2)) +
        16 / (ell n : ℝ) * (c * Real.log 2 + 1 + Real.log 2)) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      (∀ (c : ℕ) (μ : PMF (AliceProt (Inp n k) (Inp n k) (Fin k → Bool))),
        (∀ T ∈ μ.support, IsOneWayBA T) → CostLE μ c →
        (∀ X Y : Inp n k, aliceErr disjAns μ X Y ≤ ENNReal.ofReal (α / 2 ^ k)) →
        C₁ * min (n : ℝ) (1 + (n : ℝ) ^ 2 / k) ≤ c) ∧
      ∃ (c : ℕ) (μ : PMF (AliceProt (Inp n k) (Inp n k) (Fin k → Bool))),
        (∀ T ∈ μ.support, IsOneWayBA T) ∧ CostLE μ c ∧
        (∀ X Y : Inp n k, aliceErr disjAns μ X Y ≤ ENNReal.ofReal (α / 2 ^ k)) ∧
        (c : ℝ) ≤ C₂ * min (n : ℝ) (1 + (n : ℝ) ^ 2 / k)) := by sorry

end Supplement

end ElimAgree
