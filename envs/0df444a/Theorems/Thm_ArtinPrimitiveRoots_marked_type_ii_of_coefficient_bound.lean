-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_marked_type_ii_of_coefficient_bound
-- name    : ArtinPrimitiveRoots.marked_type_ii_of_coefficient_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:27:37.89285+00:00
-- url     : https://prove2.me/theorems/de7be65d-7342-4e1a-8a0a-21a355c5dbd3
-- title:
--   Lemma 10.2 (OpenAI) — coefficient criterion for the marked Type II estimate
-- statement:
--   Fix $\delta, C, D_* > 0$, $0 < q < 1$, reals $c_1 > 0$ and $c_2$, and a set $S$ of tuples $(x, H_m, H_n, \alpha, \beta)$ with $\alpha, \beta : \mathbb N \to \mathbb C$ (the permitted data). Write $L = \log x$ and $W = $ `sieveLevel x`. Assume that every tuple in $S$ satisfies
--
--   - $H_m, H_n \ge x^\delta$ and $c_1 x \le H_m H_n \le c_2 x$;
--   - for some interval $J \subseteq [H_m, 2H_m]$, $\alpha_m = 0$ unless $m \in J$ and $m$ is $W$-rough;
--   - $\beta_n = 0$ unless $n \in [H_n, 2H_n]$ and $n$ is $W$-rough;
--   - $|\alpha_m| \le L^C$ and $|\beta_n| \le L^C$ for all $m, n$.
--
--   Assume (10.6): for all $A_0, B, A > 0$ there are $C'$ and $x_0'$ such that for every tuple in $S$ with $x \ge x_0'$, every integer $k$ with $1 \le k \le L^{A_0}$, every Dirichlet character $\chi$ modulo $k$ (Mathlib's `DirichletCharacter ℂ k`, zero on nonunits), and every real $t$ with $|t| \le 2H_mH_nL^B$,
--
--   $$\Bigl|\frac{1}{H_m}\sum_{m \le 2H_m} \alpha_m \chi(m)\, m^{it}\Bigr| \le C' L^{-A}.$$
--
--   Then there is $K_0$ such that for every $K \ge \max(1, K_0)$ and all band exponents $0.1 < a_1 < \cdots < a_K < 0.2$ there are $A$ and $x_0$ such that, for every tuple in $S$ with $x \ge x_0$ and every $F : \mathbb N \to \mathbb C$ with $|F(h)| \le 1$ and $F(ph) = F(h)$ for all $h > 0$ and all $p \in \bigcup_i \mathcal P_i$ (`groupPrimes x a`),
--
--   $$\Bigl|\sum_{m \le 2H_m}\sum_{n \le 2H_n} \alpha_m \beta_n F(mn-1)\,\mathcal W(mn-1)\Bigr| \le A\, H_m H_n\, L^{-D_*},$$
--
--   where $\mathcal W$ is `mark q x a`. $K_0$ may depend on $\delta, C, D_*, q, c_1, c_2$ and $S$, but not on the $a_i$.
--
--   **Formalization note.** Hypothesis (10.6) is asymptotic and uniform over the permitted intervals and coefficients, so the coefficients are a fixed family $S$ rather than a single pair of sequences; its constant and threshold depend on $A_0, B, A$ and $S$, and the conclusion is uniform over $S$ and $F$. “Modulo $k \le L^{A_0}$” is read as $1 \le k \le L^{A_0}$. The interval support is kept as stated, through some interval $J \subseteq [H_m, 2H_m]$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 64: “Lemma 10.2 (Coefficient criterion for the marked estimate). Fix $\delta, C, D_* > 0$ and $q \in (0, 1)$. Retain the marked data and the hypotheses on $F, H_m, H_n$ in Theorem 10.1, with fixed comparison constants in $X = H_mH_n \asymp x$. Let $(\alpha_m)$ and $(\beta_n)$ be scalar sequences indexed by positive integers, supported on $W$-rough integers in their respective dyads, with $\alpha$ supported on an arbitrary interval $I \subseteq [H_m, 2H_m]$, and with $|\alpha_m|, |\beta_n| \le L^C$. Suppose that for every fixed $A_0, B, A > 0$, every Dirichlet character $\chi$ modulo $k \le L^{A_0}$, and every $|t| \le 2XL^B$, $\Bigl|\frac{1}{H_m}\sum_m \alpha_m\chi(m)m^{it}\Bigr| \ll_A L^{-A}$, (10.6) uniformly in the permitted interval, character, and frequency. The constant and threshold in this hypothesis may depend on $A_0, B, A$, the fixed setup, and all further fixed parameters defining the coefficients; these parameters are chosen before $x$ grows. Then Equation (10.5) holds when $K$ is sufficiently large in terms of the fixed data, independently of the particular band exponents $a_i$. Its implicit constant and threshold may depend on all the fixed data, including the $a_i$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 64, Lemma 10.2

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

theorem marked_type_ii_of_coefficient_bound (δ C Dstar q : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hD : 0 < Dstar) (hq0 : 0 < q) (hq1 : q < 1) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (S : Set (ℝ × ℝ × ℝ × (ℕ → ℂ) × (ℕ → ℂ)))
    (hS : ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S →
      x ^ δ ≤ Hm ∧ x ^ δ ≤ Hn ∧ c₁ * x ≤ Hm * Hn ∧ Hm * Hn ≤ c₂ * x ∧
      (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
        ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) ∧
      (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) ∧
      (∀ m, ‖α m‖ ≤ log x ^ C) ∧ (∀ n, ‖β n‖ ≤ log x ^ C))
    (hα : ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
      ∃ C' : ℝ, ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S → x₀ ≤ x →
        ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
        ∀ t : ℝ, |t| ≤ 2 * (Hm * Hn) * log x ^ B →
          ‖((1 / Hm : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1),
              α m * χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * t)‖ ≤ C' * log x ^ (-A)) :
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ A : ℝ, ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S → x₀ ≤ x →
      ∀ F : ℕ → ℂ, (∀ h, 0 < h → ‖F h‖ ≤ 1) →
        (∀ h, 0 < h → ∀ p ∈ groupPrimes x a, F (p * h) = F h) →
      ‖∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          α m * β n * F (m * n - 1) * (mark q x a (m * n - 1) : ℂ)‖ ≤
        A * (Hm * Hn) * log x ^ (-Dstar) := by
  sorry

end ArtinPrimitiveRoots
