-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_major_square_bound
-- name    : ArtinPrimitiveRoots.major_square_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T17:02:40.481732+00:00
-- url     : https://prove2.me/theorems/198c4004-f8c6-4495-8f20-54e8baee345f
-- title:
--   (10.10), proof of Lemma 10.2 (OpenAI) — for coefficients satisfying (10.6), the major form Q_Y^maj is at most c·H_mH_nY·(log x)^{−D}
-- statement:
--   Fix $\delta, C, c_1 > 0$, $c_2$, and a set $S$ of tuples $(x, H_m, H_n, \alpha, \beta)$ satisfying the hypotheses of Lemma 10.2 (`marked_type_ii_of_coefficient_bound`): $H_m, H_n \ge x^\delta$, $c_1x \le H_mH_n \le c_2x$, $\alpha$ supported on $W$-rough integers of an interval $J \subseteq [H_m, 2H_m]$, $\beta$ on $W$-rough integers of $[H_n, 2H_n]$, $|\alpha_m|, |\beta_n| \le L^C$, and the cancellation (10.6) of $\alpha$ against characters of modulus at most $L^{A_0'}$ at frequencies $|t| \le 2H_mH_nL^B$. Then for every $A_0 > 0$, $D > 0$, $K \ge 1$ and band exponents $0.1 < a_1 < \dots < a_K < 0.2$ there are $c$ and $x_0$ such that for every tuple in $S$ with $x \ge x_0$ and every $Y \ge 1$,
--
--   $$|Q_Y^{\mathrm{maj}}| \le c\,H_mH_nY\,L^{-D},$$
--
--   with $Q_Y^{\mathrm{maj}} = $ `majorSquare x a A₀ Y Hm Hn α β` (bundle `Def_ArtinMarkedSquare`).
--
--   This is [21, Proposition 5.1], equation (5.2), with (10.6) in the role of [21, Lemma 5.2], as the paper's proof of Lemma 10.2 uses it. A step toward `marked_type_ii_of_coefficient_bound`.
--
--   **Formalization note.** The coefficients form a family $S$ with hypotheses copied from Lemma 10.2, because (10.6) is used at accuracies chosen inside the proof. The bound holds for every fixed $A_0$ and $K$, so it can be applied after (10.9) fixes them.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 66: “The major-term proof therefore gives $|Q_Y^{\mathrm{maj}}| \ll_D XYL^{-D}$ (10.10) for every fixed $D > 0$.” OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 33, Proposition 5.1: “For every fixed $D > 0$, the unrestricted major sum $Q_Y^{\mathrm{maj}} = \bigl(\prod_{i=1}^KV_i^{-2}\bigr)\sum_{a,b,m,n,r,s}\eta(a/Y)\eta(b/Y)\alpha_m\alpha_r\beta_n\beta_sH_{\mathfrak M}(bmn - ars; a, b)$ (5.1) satisfies $|Q_Y^{\mathrm{maj}}| \ll_D XYL^{-D}$. (5.2)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 66, proof of Lemma 10.2, (10.10)

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare

namespace ArtinPrimitiveRoots

open Real

theorem major_square_bound (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
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
    ∀ A₀ : ℝ, 0 < A₀ → ∀ D : ℝ, 0 < D → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S → x₀ ≤ x →
        ∀ Y : ℝ, 1 ≤ Y →
          ‖majorSquare x a A₀ Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-D)) := by
  sorry

end ArtinPrimitiveRoots
