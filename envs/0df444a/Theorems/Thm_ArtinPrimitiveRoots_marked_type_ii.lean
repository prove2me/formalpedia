-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_marked_type_ii
-- name    : ArtinPrimitiveRoots.marked_type_ii
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:28:02.609804+00:00
-- url     : https://prove2.me/theorems/3ef79b57-6d22-4d98-92dc-35e85e6cd421
-- title:
--   Theorem 10.1 (OpenAI) — one-sided marked Type II estimate
-- statement:
--   Fix $\delta, C, D_* > 0$ and $0 < q < 1$. There is $K_0$ such that for every $K \ge \max(1, K_0)$, all band exponents $0.1 < a_1 < \cdots < a_K < 0.2$, and all reals $c_1 > 0$ and $c_2$, there are $A$ and $x_0$ with the following property. Let $x \ge x_0$, $L = \log x$, $W = $ `sieveLevel x`, $V = $ `mertensProduct`, and let $\mathcal W$ be the mark `mark q x a`. Let
--
--   - $H_m, H_n \ge x^\delta$ be reals with $c_1 x \le H_m H_n \le c_2 x$;
--   - $F : \mathbb N \to \mathbb C$ satisfy $|F(h)| \le 1$ and $F(ph) = F(h)$ for every $h > 0$ and every group prime $p \in \bigcup_i \mathcal P_i$ (`groupPrimes x a`);
--   - $J \subseteq [H_m, 2H_m]$ be an interval (an order-connected set of reals) and $v$ a real with $|v| \le L^C$;
--   - $\beta : \mathbb N \to \mathbb C$ satisfy $|\beta_n| \le L^C$ for all $n$ and vanish except at $W$-rough $n \in [H_n, 2H_n]$.
--
--   Put $\alpha_m = m^{iv}\bigl(\mathbf 1_{m \text{ prime}} - \mathbf 1_{P^-(m) > W}/(V(W)\log m)\bigr)$ for $m \in J$ and $\alpha_m = 0$ otherwise. Then
--
--   $$\Bigl|\sum_{m \le 2H_m}\sum_{n \le 2H_n} \alpha_m \beta_n F(mn-1)\,\mathcal W(mn-1)\Bigr| \le A\, H_m H_n\, L^{-D_*}.$$
--
--   $K_0$ depends only on $\delta, C, D_*, q$. $A$ and $x_0$ may also depend on $K$, the $a_i$, $c_1$ and $c_2$, and are uniform in $H_m$, $H_n$, $F$, $J$, $v$ and $\beta$.
--
--   **Formalization note.** $X = H_m H_n \asymp x$ is read as $c_1 x \le H_m H_n \le c_2 x$ with comparison constants fixed before $x$. The uniformity in $F$, the interval and the coefficients, and the invariance of $F$ only at positive $h$, follow the paragraph after the theorem (p. 64): “The invariance is required for every positive $h$, including when $p \mid h$. The estimate is uniform over the permitted $F$, coefficient intervals, and coefficients.” The ranges $m \le 2H_m$, $n \le 2H_n$ contain the supports of $\alpha$ and $\beta$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 64: “Theorem 10.1 (One-sided marked Type II estimate). Fix $\delta, C, D_* > 0$ and $q \in (0, 1)$. Suppose $H_m, H_n \ge x^\delta$ and $X = H_mH_n \asymp x$. Let $F$ satisfy $|F(h)| \le 1$ and $F(ph) = F(h)$ for every prime in the groups defined in Equation (10.2). Let $\alpha_m$ be supported on an arbitrary interval in $[H_m, 2H_m]$, where it has the value $\alpha_m = m^{iv}\Bigl(\mathbf 1_{m \text{ prime}} - \frac{\mathbf 1_{P^-(m)>W}}{V(W)\log m}\Bigr)$, $|v| \le L^C$. Let $\beta_n$ be supported on $W$-rough integers in $[H_n, 2H_n]$, with $|\beta_n| \le L^C$. If $K$ is sufficiently large in terms of $\delta, C, D_*, q$, then $\Bigl|\sum_{m,n}\alpha_m\beta_n F(mn-1)\mathcal W(mn-1)\Bigr| \ll XL^{-D_*}$. (10.5) The required lower bound on $K$ is independent of the particular $a_i$. The implicit constant and the threshold for $x$ may depend on all the fixed parameters, including the $a_i$.”
--
--   The paper imports this result: “The following is the one-sided marked Type II estimate of *The Poisson–Dirichlet law for the prime factors of $p - 1$* [21, Theorem 3.1].” That is OpenAI, *The Poisson–Dirichlet law for the prime factors of p − 1*, Theorem 3.1.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 64, Theorem 10.1 (from OpenAI, The Poisson–Dirichlet law for the prime factors of p−1, Theorem 3.1)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem marked_type_ii (δ C Dstar q : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ c₁ c₂ : ℝ, 0 < c₁ →
      ∃ A : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ Hm Hn : ℝ, x ^ δ ≤ Hm → x ^ δ ≤ Hn → c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      ∀ F : ℕ → ℂ, (∀ h, 0 < h → ‖F h‖ ≤ 1) →
        (∀ h, 0 < h → ∀ p ∈ groupPrimes x a, F (p * h) = F h) →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc Hm (2 * Hm) →
      ∀ v : ℝ, |v| ≤ log x ^ C →
      ∀ β : ℕ → ℂ,
        (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
        (∀ n, ‖β n‖ ≤ log x ^ C) →
      ‖∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          (if (m : ℝ) ∈ J then
            (m : ℂ) ^ (Complex.I * v) *
              ((if m.Prime then 1 else 0) -
                (if IsRough (sieveLevel x) m then 1 else 0) /
                  ((mertensProduct (sieveLevel x) * log m : ℝ) : ℂ))
          else 0) *
          β n * F (m * n - 1) * (mark q x a (m * n - 1) : ℂ)‖ ≤
        A * (Hm * Hn) * log x ^ (-Dstar) := by
  sorry

end ArtinPrimitiveRoots
