-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_square_major_replacement
-- name    : ArtinPrimitiveRoots.square_major_replacement
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T17:03:38.305098+00:00
-- url     : https://prove2.me/theorems/0ed7f3cf-2bc9-4451-b477-b542c192df1f
-- title:
--   (10.9), proof of Lemma 10.2 (OpenAI) — the expanded square Q_Y differs from its major form Q_Y^maj by at most c·H_mH_nY·(log x)^{−A}, for suitable A₀ and all large K
-- statement:
--   Fix $\delta, C, c_1 > 0$ and $c_2$. For every $A > 0$ there are $A_0 > 0$ and $K_0$ such that for every $K \ge \max(1, K_0)$ and all band exponents $0.1 < a_1 < \dots < a_K < 0.2$ there are $c$ and $x_0$ with the following property. Let $x \ge x_0$, $L = \log x$, $W = $ `sieveLevel x`, and $H_m, H_n \ge x^\delta$ with $c_1x \le H_mH_n \le c_2x$. Let $\alpha, \beta : \mathbb N \to \mathbb C$ with $|\alpha_m|, |\beta_n| \le L^C$, with $\alpha$ supported on $W$-rough integers in some interval $J \subseteq [H_m, 2H_m]$ and $\beta$ on $W$-rough integers in $[H_n, 2H_n]$. Then for every $Y \ge 1$,
--
--   $$|Q_Y - Q_Y^{\mathrm{maj}}| \le c\,H_mH_nY\,L^{-A},$$
--
--   with $Q_Y = $ `expandedSquare x a Y Hm Hn α β` and $Q_Y^{\mathrm{maj}} = $ `majorSquare x a A₀ Y Hm Hn α β` (bundle `Def_ArtinMarkedSquare`).
--
--   This is [21, Proposition 4.1], equation (4.2), for general rough coefficients, as the paper's proof of Lemma 10.2 uses it. A step toward `marked_type_ii_of_coefficient_bound` (Lemma 10.2).
--
--   **Formalization note.** $A_0$ and then $K$ are chosen after the accuracy $A$ and independently of the band exponents, which only affect $c$ and $x_0$, as [21, Proposition 4.1] says. The statement is asserted for every $Y \ge 1$; both squares vanish unless $Y$ is within a factor 4 of a product of one prime per group.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), pp. 65–66: “Thus the replacement conclusion, including restoration of independent $a, b$, gives $|Q_Y - Q_Y^{\mathrm{maj}}| \ll_A XYL^{-A}$ (10.9) for every prescribed fixed accuracy, with the choices specified below.” OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 19, Proposition 4.1: “For every fixed $E_0 > 0$, one can choose $A_0$ sufficiently large and then $K$ sufficiently large, in terms of $E_0$, $q$ and the fixed parameters of Theorem 3.1 […] The choices of $A_0, K$ do not depend on the particular fixed band exponents $a_1 < \cdots < a_K$; the threshold for $x$ may depend on them.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 65, proof of Lemma 10.2, (10.9)

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare

namespace ArtinPrimitiveRoots

open Real

theorem square_major_replacement (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖expandedSquare x a Y Hm Hn α β - majorSquare x a A₀ Y Hm Hn α β‖ ≤
              c * (Hm * Hn * Y * log x ^ (-A)) := by
  sorry

end ArtinPrimitiveRoots
