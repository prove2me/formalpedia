-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_type_ii_progression
-- name    : ArtinPrimitiveRoots.type_ii_progression
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:27:20.981141+00:00
-- url     : https://prove2.me/theorems/c4244419-aae3-42ab-a7ee-7e5f6252457c
-- title:
--   Lemma 12.1 (OpenAI) — Type II estimate in the progression
-- statement:
--   Let $M, c, u$ satisfy (12.1): $M > 0$, $8 \mid M$, $c \in \{2, 4\}$, $(u, M) = 1$, $c \mid u - 1$ and $\bigl(\frac{u-1}{c}, \frac Mc\bigr) = 1$. Let $\Psi : \mathbb R \to \mathbb R$ be $C^\infty$ with closed support in $(1, 2)$, $0 \le \Psi \le 1$ and $\int \Psi > 0$. Fix reals $\delta > 0$, $0 < \gamma < s_- < s_+ < 1$ (`sMinus`, `sPlus`), $c_1 > 0$ and $c_2$.
--
--   There is $K_0$ such that for every $K \ge \max(1, K_0)$ and all band exponents $0.1 < a_1 < \cdots < a_K < 0.2$ there are $A$ and $x_0$ such that the following holds for every $x \ge x_0$, with $L = \log x$ and $W = $ `sieveLevel x`. For all reals $H_m, H_n \ge x^\delta$ with $c_1 x \le H_m H_n \le c_2 x$, every interval $J \subseteq [H_m, 2H_m]$ (an order-connected set of reals), if $s_- \le \log H_m/L$ and $\log(2H_m)/L \le s_+$, and for every $b : \mathbb N \to \mathbb C$ with $|b_n| \le 1$ that vanishes except at $W$-rough $n \in [H_n, 2H_n]$,
--
--   $$\Bigl|\sum_{m \le 2H_m,\ m \in J}\ \sum_{n \le 2H_n} \bigl(R_\gamma(m) - B_\gamma(m)\bigr)\, b_n\, w(mn)\Bigr| \le A\, H_m H_n\, L^{-6},$$
--
--   where $R_\gamma = $ `roughIndicator x γ`, $B_\gamma = $ `roughProxy x γ`, and $w = $ `constructionWeight M c u Ψ x a` (marks with $q = 1/2$).
--
--   $K_0$ depends on $M, c, u, \Psi, \delta, \gamma, s_\pm, c_1, c_2$ but not on the $a_i$; $A$ and $x_0$ may also depend on the $a_i$, and are uniform in $H_m$, $H_n$, $J$ and $b$.
--
--   **Formalization note.** $X = H_mH_n \asymp x$ with fixed comparison constants is $c_1 x \le H_m H_n \le c_2 x$. The containment (12.6) is written as its two endpoint inequalities. The coprimality conditions are `IsCoprime` over $\mathbb Z$, with exact integer quotients.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 75: “Lemma 12.1 (Type II estimate in the progression). Fix $\delta > 0$ and $0 < \gamma < s_- < s_+ < 1$. Let $H_m, H_n \ge x^\delta$, with $X = H_mH_n \asymp x$ and fixed comparison constants, and let $I \subseteq [H_m, 2H_m]$ be an interval. Suppose $[\log H_m/L, \log(2H_m)/L] \subseteq [s_-, s_+]$. (12.6) Let $|b_n| \le 1$ be supported on $W$-rough integers in $[H_n, 2H_n]$. For sufficiently large $K$, $\Bigl|\sum_{m \in I, n}\bigl(R_\gamma(m) - B_\gamma(m)\bigr)b_n w(mn)\Bigr| \ll XL^{-6}$. (12.7) This is uniform in the dyads, interval, and coefficients. The lower bound on $K$ is independent of the $a_i$. Constants and thresholds may depend on all fixed parameters, including the band exponents.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 75, Lemma 12.1

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem type_ii_progression (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y)
    (δ γ sMinus sPlus : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hγs : γ < sMinus) (hss : sMinus < sPlus) (hsPlus : sPlus < 1)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) :
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ A : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ Hm Hn : ℝ, x ^ δ ≤ Hm → x ^ δ ≤ Hn → c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc Hm (2 * Hm) →
      sMinus ≤ log Hm / log x → log (2 * Hm) / log x ≤ sPlus →
      ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) →
        (∀ n, b n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
      ‖∑ m ∈ (Finset.range (⌊2 * Hm⌋₊ + 1)).filter (fun m : ℕ => (m : ℝ) ∈ J),
          ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * b n *
            (constructionWeight M c u Ψ x a (m * n) : ℂ)‖ ≤
        A * (Hm * Hn) * log x ^ (-6 : ℝ) := by
  sorry

end ArtinPrimitiveRoots
