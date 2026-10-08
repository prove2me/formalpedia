-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_rough_pairs_upper_bound
-- name    : ArtinPrimitiveRoots.rough_pairs_upper_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:27:29.0924+00:00
-- url     : https://prove2.me/theorems/1821f5f2-4140-44db-932f-438663f70b38
-- title:
--   Lemma 12.5 (OpenAI) — upper bound for rough pairs
-- statement:
--   Let $M > 0$ with $8 \mid M$, and let $\Psi$ be $C^\infty$ with closed support in $(1, 2)$, $0 \le \Psi \le 1$ and $\int\Psi > 0$. There is $C_1$, depending only on $M$ and $\Psi$, such that the following holds for all $c \in \{2, 4\}$ and $u$ with $(u, M) = 1$, $c \mid u - 1$, $\bigl(\frac{u-1}{c}, \frac Mc\bigr) = 1$, every $K \ge 1$ and all $0.1 < a_1 < \cdots < a_K < 0.2$. There is $x_0$ such that for every $x \ge x_0$ and all reals $M_1, M_2$ with
--
--   $$x/4 \le M_1M_2 \le 2x,\qquad x^{0.46}/2 \le M_i \le 2x^{0.54}\quad(i = 1, 2),$$
--
--   we have
--
--   $$\sum_{\substack{M_1 \le m < 2M_1,\ M_2 \le n < 2M_2\\ P^-(m) > W,\ P^-(n) > W}} w(mn) \le C_1\,X_0\,V(W)^2,$$
--
--   where $W = $ `sieveLevel x`, $V = $ `mertensProduct`, $w = $ `constructionWeight M c u Ψ x a` and $X_0 = $ `totalMass M c u Ψ x a`.
--
--   **Formalization note.** $M_1$ and $M_2$ are arbitrary reals in the range (12.28): the box $[M_1, 2M_1) \times [M_2, 2M_2)$ is not required to have $M_i$ a power of $2$. $C_1$ is chosen before $c$, $u$, $K$ and the $a_i$; the parameters $\kappa, b, \varepsilon$ do not occur in the statement. The threshold $x_0$ is the section's standing convention.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 82: “Lemma 12.5 (An upper bound for rough pairs). Let $\mathcal B = [M_1, 2M_1) \times [M_2, 2M_2)$ be any dyadic box such that $x/4 \le M_1M_2 \le 2x$, $x^{0.46}/2 \le M_i \le 2x^{0.54}$ $(i = 1, 2)$. (12.28) Then $\sum_{(m,n) \in \mathcal B,\ P^-(m)>W,\ P^-(n)>W} w(mn) \le C_1X_0V(W)^2$, (12.29) where $C_1$ depends at most on $M, \Psi$, and is independent of $K, \kappa, b, \varepsilon$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 82, Lemma 12.5

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem rough_pairs_upper_bound (M : ℕ) (hM : 0 < M) (h8 : 8 ∣ M)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) :
    ∃ C₁ : ℝ, ∀ (c : ℕ) (u : ℤ), (c = 2 ∨ c = 4) → IsCoprime u M → (c : ℤ) ∣ u - 1 →
        IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
      ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ M₁ M₂ : ℝ, x / 4 ≤ M₁ * M₂ → M₁ * M₂ ≤ 2 * x →
        x ^ (0.46 : ℝ) / 2 ≤ M₁ → M₁ ≤ 2 * x ^ (0.54 : ℝ) →
        x ^ (0.46 : ℝ) / 2 ≤ M₂ → M₂ ≤ 2 * x ^ (0.54 : ℝ) →
        ∑ m ∈ (Finset.range ⌈2 * M₁⌉₊).filter
              (fun m : ℕ => M₁ ≤ m ∧ (m : ℝ) < 2 * M₁ ∧ IsRough (sieveLevel x) m),
          ∑ n ∈ (Finset.range ⌈2 * M₂⌉₊).filter
              (fun n : ℕ => M₂ ≤ n ∧ (n : ℝ) < 2 * M₂ ∧ IsRough (sieveLevel x) n),
            constructionWeight M c u Ψ x a (m * n) ≤
          C₁ * totalMass M c u Ψ x a * mertensProduct (sieveLevel x) ^ 2 := by
  sorry

end ArtinPrimitiveRoots
