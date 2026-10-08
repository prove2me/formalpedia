-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_balanced_cost
-- name    : ArtinPrimitiveRoots.balanced_cost
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:19:55.493425+00:00
-- url     : https://prove2.me/theorems/0445a9c5-107a-40b5-9197-84ad646ca39c
-- title:
--   Proof of Proposition 2.1 (OpenAI), (12.33) — composites with two nearly equal prime factors
-- statement:
--   Let $M, c, u$ satisfy (12.1): $M > 0$, $8 \mid M$, $c \in \{2, 4\}$, $(u, M) = 1$, $c \mid u - 1$ and $\bigl(\frac{u-1}{c}, \frac Mc\bigr) = 1$. Let $\Psi$ be $C^\infty$ with closed support in $(1, 2)$, $0 \le \Psi \le 1$ and $\int\Psi > 0$. Then there is $C_2 > 0$ with the following property. For every $0 < \kappa < 0.01$ there is $K_0$ such that for every $K \ge \max(K_0, 1)$, all $0.1 < a_1 < \cdots < a_K < 0.2$ and every $\eta > 0$ there is $x_0$ such that for every $x \ge x_0$, with $L = \log x$,
--
--   $$\sum_{\substack{P^-(d) > x^{1/2-\kappa}\\ d \text{ not prime}}} w(d) \;\le\; C_2\bigl(\kappa + L^{-1}\bigr)\frac{X_0}{L} + \eta\,\frac{X_0}{L}.$$
--
--   Here $w = $ `constructionWeight M c u Ψ x a`, $X_0 = $ `totalMass M c u Ψ x a`, and $P^-(d) > y$ is `IsRough y d`: $d \ge 1$ and every prime factor of $d$ exceeds $y$. The sum is a `tsum` over all natural numbers $d$.
--
--   **Formalization note.** The $o(X_0/L)$ of (12.33) is written as $\eta X_0/L$ for $x \ge x_0(\eta)$. "$d$ composite" is "$d$ not prime"; the only other $d$ allowed is $d = 1$, where $w(1) = 0$ by definition. $C_2$ is chosen after $M, c, u, \Psi$ and before $\kappa$, $K$ and the marks, so it is independent of $K$ and $\kappa$ as the paper says. The paper's $C_2$ depends only on $M$ and $\Psi$. Here it may also depend on $c$ and $u$, which are fixed throughout Proposition 2.1. The bound holds once $K$ is large in terms of $\kappa$ ($K \ge K_0$), as the completion in §12.6 allows. Of the standing assumptions (12.11), $0 < \kappa < 0.01$ is included; $b$ and $\varepsilon$ do not occur in the statement.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 84: “Summing the boxes gives $\sum_{P^-(d)>x^{1/2-\kappa},\ d \text{ composite}} w(d) \le C_2(\kappa + L^{-1})\frac{X_0}{L} + o(X_0/L)$, (12.33) where $C_2 = (0.46)^{-2}C_1C_{\mathrm{dyad}}$ depends at most on $M, \Psi$, and is independent of $K, \kappa, b, \varepsilon$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 84, proof of Proposition 2.1, (12.33)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem balanced_cost (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ κ : ℝ, 0 < κ → κ < 0.01 →
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∑' d : ℕ, (if IsRough (x ^ (1 / 2 - κ)) d ∧ ¬ d.Prime then
            constructionWeight M c u Ψ x a d else 0) ≤
          C₂ * (κ + 1 / log x) * (totalMass M c u Ψ x a / log x) +
            η * (totalMass M c u Ψ x a / log x) := by
  sorry

end ArtinPrimitiveRoots
