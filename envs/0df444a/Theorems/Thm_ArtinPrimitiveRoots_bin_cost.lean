-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_bin_cost
-- name    : ArtinPrimitiveRoots.bin_cost
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:20:04.964142+00:00
-- url     : https://prove2.me/theorems/2e494b3c-95b9-46c1-b5f9-1abe7ced2705
-- title:
--   Proof of Proposition 2.1 (OpenAI), (12.24) — the cost of one bin of least prime factors
-- statement:
--   Let $M, c, u$ satisfy (12.1): $M > 0$, $8 \mid M$, $c \in \{2, 4\}$, $(u, M) = 1$, $c \mid u - 1$ and $\bigl(\frac{u-1}{c}, \frac Mc\bigr) = 1$. Let $\Psi$ be $C^\infty$ with closed support in $(1, 2)$, $0 \le \Psi \le 1$ and $\int\Psi > 0$. Let $0 < \kappa < 0.01$, $0 < b < 0.01$ and $b \le \gamma < \gamma' \le 1/2 - \kappa$. Then there is $K_0$ such that for every $K \ge \max(K_0, 1)$, all $0.1 < a_1 < \cdots < a_K < 0.2$ and every $\eta > 0$ there is $x_0$ such that for every $x \ge x_0$,
--
--   $$T_{\gamma,\gamma'} := \sum_{\substack{x^\gamma < n \le x^{\gamma'}\\ n \text{ prime}}}\ \sum_{P^-(m) > x^\gamma} w(mn) \;\le\; \frac{\mathfrak S_M X_0}{\log x}\Bigl(\sup_{\gamma \le t \le \gamma'} D_\gamma(1 - t)\,\log\frac{\gamma'}{\gamma} + \eta\Bigr).$$
--
--   Here $w = $ `constructionWeight M c u Ψ x a`, $X_0 = $ `totalMass M c u Ψ x a`, $\mathfrak S_M = $ `singularSeries M`, $D_\gamma = $ `roughDensity γ`, and $P^-(m) > y$ is `IsRough y m`: $m \ge 1$ and every prime factor of $m$ exceeds $y$. The inner sum is a `tsum` over all natural numbers $m$, and the supremum is `sSup` of the image of $[\gamma, \gamma']$.
--
--   **Formalization note.** The $o(1)$ of (12.24) is written as $\eta$ for $x \ge x_0(\eta)$. A bin $(\gamma, \gamma'] \subseteq (b, 1/2 - \kappa]$ whose left endpoint may equal $b$ is $b \le \gamma < \gamma' \le 1/2 - \kappa$. The bound holds once $K$ is large in terms of the fixed parameters ($K \ge K_0$), as the completion in §12.6 allows ("Choose $K$ sufficiently large for all of them"). Of the standing assumptions (12.11), $0 < \kappa < 0.01$ and $0 < b < 0.01$ are included; $\varepsilon$ does not occur in the statement and is omitted.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), pp. 80–81: “For a bin $(\gamma, \gamma'] \subseteq (b, 1/2 - \kappa]$, with the first left endpoint allowed to equal $b$, define $T_{\gamma,\gamma'} = \sum_{x^\gamma < n \le x^{\gamma'},\ n \text{ prime}}\ \sum_{P^-(m) > x^\gamma} w(mn)$. […] Since $n > W$, the remaining roughness condition is precisely $P^-(mn) > W$. Lemma 12.4 thus gives $T_{\gamma,\gamma'} \le \frac{\mathfrak S_M X_0}{L}\Bigl\{\sup_{\gamma\le t\le\gamma'} D_\gamma(1 - t)\log\frac{\gamma'}{\gamma} + o(1)\Bigr\}$. (12.24)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 80–81, proof of Proposition 2.1, (12.24)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem bin_cost (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y)
    (κ b γ γ' : ℝ) (hκ : 0 < κ) (hκ' : κ < 0.01) (hb : 0 < b) (hb' : b < 0.01)
    (hbγ : b ≤ γ) (hγγ' : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
            ∑' m : ℕ, (if IsRough (x ^ γ) m then constructionWeight M c u Ψ x a (m * n) else 0)
          ≤ singularSeries M * totalMass M c u Ψ x a / log x *
            (sSup ((fun t => roughDensity γ (1 - t)) '' Set.Icc γ γ') * log (γ' / γ) + η) := by
  sorry

end ArtinPrimitiveRoots
