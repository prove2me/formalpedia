-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_rough_factor_type_ii
-- name    : ArtinPrimitiveRoots.rough_factor_type_ii
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:28:29.699429+00:00
-- url     : https://prove2.me/theorems/07399099-389b-4ac0-a0f2-e48593789e84
-- title:
--   Proposition 10.3 (OpenAI) — rough-factor Type II estimate
-- statement:
--   Fix $\delta, C, D_* > 0$, $0 < q < 1$, reals $0 < \gamma < w_- < w_+ < 1$ (`wMinus`, `wPlus`), and reals $c_1 > 0$ and $c_2$. There is $K_0$ such that for every $K \ge \max(1, K_0)$ and all band exponents $0.1 < a_1 < \cdots < a_K < 0.2$ there are $A$ and $x_0$ with the following property. Let $x \ge x_0$, $L = \log x$, $W = $ `sieveLevel x`, $V = $ `mertensProduct`, $D_\gamma = $ `roughDensity γ`, and let $\mathcal W$ be `mark q x a`. Let
--
--   - $H_m, H_n \ge x^\delta$ be reals with $c_1 x \le H_m H_n \le c_2 x$, $w_- \le \log H_m / L$ and $\log(2H_m)/L \le w_+$;
--   - $F : \mathbb N \to \mathbb C$ satisfy $|F(h)| \le 1$ and $F(ph) = F(h)$ for every $h > 0$ and every $p \in \bigcup_i \mathcal P_i$ (`groupPrimes x a`);
--   - $J \subseteq [H_m, 2H_m]$ be an interval (an order-connected set of reals) and $v$ a real with $|v| \le L^C$;
--   - $\beta : \mathbb N \to \mathbb C$ satisfy $|\beta_n| \le L^C$ for all $n$ and vanish except at $W$-rough $n \in [H_n, 2H_n]$.
--
--   Put $\alpha_m = m^{iv}\Bigl(\mathbf 1_{P^-(m) > x^\gamma} - \frac{D_\gamma(\log m/L)}{L\,V(W)}\mathbf 1_{P^-(m) > W}\Bigr)$ for $m \in J$ and $\alpha_m = 0$ otherwise. Then
--
--   $$\Bigl|\sum_{m \le 2H_m}\sum_{n \le 2H_n} \alpha_m \beta_n F(mn-1)\,\mathcal W(mn-1)\Bigr| \le A\, H_m H_n\, L^{-D_*}.$$
--
--   $K_0$ depends on the fixed data $\delta, C, D_*, q, \gamma, w_\pm, c_1, c_2$ but not on the $a_i$; $A$ and $x_0$ may depend on all of these and the $a_i$, and are uniform in $H_m$, $H_n$, $F$, $J$, $v$ and $\beta$.
--
--   **Formalization note.** The containment $[\log H_m/L, \log(2H_m)/L] \subseteq [w_-, w_+]$ is written as its two endpoint inequalities. The inherited data of Theorem 10.1 (`ArtinPrimitiveRoots.marked_type_ii`) are encoded as there, with the comparison constants $c_1, c_2$ fixed before $K$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 67: “Proposition 10.3 (A rough-factor Type II estimate). Retain the marked data and all the hypotheses on $F, \beta, H_m, H_n$ of Theorem 10.1. Fix real numbers $0 < \gamma < w_- < w_+ < 1$, and suppose $[\log H_m/L, \log(2H_m)/L] \subseteq [w_-, w_+]$. On an arbitrary interval $I \subseteq [H_m, 2H_m]$, set $\alpha_m = m^{iv}\Bigl(\mathbf 1_{P^-(m)>x^\gamma} - \frac{D_\gamma(\log m/L)}{LV(W)}\mathbf 1_{P^-(m)>W}\Bigr)$, $|v| \le L^C$, (10.13) and set $\alpha_m = 0$ outside $I$. Then Equation (10.5) holds for every fixed $D_* > 0$ when $K$ is sufficiently large in terms of the fixed data. Its required lower bound is independent of the particular band exponents $a_i$; the threshold and implicit constant may depend on all the fixed data. In particular, $\gamma$ and the gap $w_- - \gamma$ are fixed before $x$ grows.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 67, Proposition 10.3

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem rough_factor_type_ii (δ C Dstar q : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hq0 : 0 < q) (hq1 : q < 1) (γ wMinus wPlus : ℝ) (hγ : 0 < γ) (hγw : γ < wMinus) (hww : wMinus < wPlus)
    (hwPlus : wPlus < 1) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) :
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ A : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ Hm Hn : ℝ, x ^ δ ≤ Hm → x ^ δ ≤ Hn → c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      wMinus ≤ log Hm / log x → log (2 * Hm) / log x ≤ wPlus →
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
              ((if IsRough (x ^ γ) m then 1 else 0) -
                ((roughDensity γ (log m / log x) /
                    (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
                  (if IsRough (sieveLevel x) m then 1 else 0))
          else 0) *
          β n * F (m * n - 1) * (mark q x a (m * n - 1) : ℂ)‖ ≤
        A * (Hm * Hn) * log x ^ (-Dstar) := by
  sorry

end ArtinPrimitiveRoots
