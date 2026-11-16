-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_B_4
-- name    : ElimAgree.Supplement.theorem_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:41:59.121259+00:00
-- url     : https://prove2.me/theorems/2231f588-82e4-489b-b4f8-954632e83d00
-- title:
--   Theorem B.4 (Hashing tail) — $(H_\Phi)$ with $\Phi=2^{17}k2^k$
-- statement:
--   Let $X$ be uniform in $\mathbb F_2^{k\times n}$ and $Q=2^k$. For every nonempty $B\subseteq\mathbb F_2^n$ and every $0<\tau<1$,
--
--   $$\Pr_X\Big[\max_\sigma\Big|Q\Pr_{y\in B}[Xy=\sigma]-1\Big|>\tau\Big]\ \le\ \min\Big\{1,\ \frac{2^{17}k2^k}{\tau^2|B|}\Big\}.$$
--
--   In particular the hashing bound $(H_\Phi)$ holds with $\Phi=2^{17}k2^k$.
--
--   The failure probability is linear in $k2^k/|B|$ uniformly in $n$, $k$ and $\tau$, which is what the leaf accounting of Lemma B.3 needs.
--
--   **Formalization Note** $\max_\sigma|\cdot|>\tau$ is "some $\sigma$ has $|\cdot|>\tau$"; probabilities are counting fractions.
--
--   Differences from the source: none.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem B.4, p.33 (PDF p.35); (H_Φ), p.32 (PDF p.34)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_REIP

namespace ElimAgree

namespace Supplement

/-- Theorem B.4 (Hashing tail), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.33. For every nonempty `B ⊆ F_2^n` and every `0 < τ < 1`,
`Pr_X[max_σ |Q Pr_{y∈B}[Xy = σ] − 1| > τ] ≤ min{1, 2^{17}k2^k/(τ²|B|)}`, with `X` uniform in
`F_2^{k×n}` and `Q = 2^k`. In particular `(H_Φ)` holds with `Φ = 2^{17}k2^k`.

**Formalization Note.** `max_σ |…| > τ` over the finite set `F_2^k` is written as "some `σ` has
`|…| > τ`". `B` may contain `0` here; `(H_Φ)` quantifies over `B ⊆ F_2^n ∖ {0}`. -/
theorem theorem_B_4 :
    (∀ (n k : ℕ) (B : Finset (Vec n)), B.Nonempty → ∀ τ : ℝ, 0 < τ → τ < 1 →
      probX (fun X : Mat k n => ∃ σ : Fin k → ZMod 2, τ < |(2 : ℝ) ^ k * probInB B X σ - 1|) ≤
        min 1 ((2 : ℝ) ^ 17 * k * 2 ^ k / (τ ^ 2 * B.card))) ∧
    (∀ n k : ℕ, HPhi n k ((2 : ℝ) ^ 17 * k * 2 ^ k)) := by sorry

end Supplement

end ElimAgree
