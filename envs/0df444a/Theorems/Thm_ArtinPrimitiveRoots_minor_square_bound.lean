-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_minor_square_bound
-- name    : ArtinPrimitiveRoots.minor_square_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T18:01:57.674268+00:00
-- url     : https://prove2.me/theorems/f36a0234-7c9f-4aea-91a5-e700d85e441a
-- title:
--   (10.9) for the coprime minor-arc part, proof of Lemma 10.2 (OpenAI) — Q_Y^min is at most c·H_mH_nY·(log x)^{−A}, for suitable A₀ and all large K
-- statement:
--   Fix $\delta, C, c_1 > 0$ and $c_2$. For every $A > 0$ there are $A_0 > 0$ and $K_0$ such that for every $K \ge \max(1, K_0)$ and all band exponents $0.1 < a_1 < \dots < a_K < 0.2$ there are $c$ and $x_0$ with the following property. For $x \ge x_0$, $L = \log x$, $H_m, H_n \ge x^\delta$ with $c_1x \le H_mH_n \le c_2x$, and $\alpha, \beta$ supported on $W$-rough integers of $[H_m, 2H_m]$ (on some interval) and $[H_n, 2H_n]$, with $|\alpha_m|, |\beta_n| \le L^C$, and every $Y \ge 1$:
--
--   $$|Q_Y^{\min}| \le c\,H_mH_nY\,L^{-A},$$
--
--   with $Q_Y^{\min} = $ `minorSquare x a A₀ Y Hm Hn α β` (bundle `Def_ArtinMinorSquare`).
--
--   This is the core of [21, Proposition 4.1]: the content of §§3.2–4.9 of OpenAI's *The Poisson–Dirichlet law for prime predecessors*. A step toward `square_major_replacement` (10.9). The shared-label parts of $Q_Y - Q_Y^{\mathrm{maj}}$ are bounded separately, so (10.9) follows from this statement.
--
--   **Formalization note.** The hypotheses and the order of constants are those of `square_major_replacement`.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 65: “Thus the replacement conclusion, including restoration of independent $a, b$, gives $|Q_Y - Q_Y^{\mathrm{maj}}| \ll_A XYL^{-A}$ (10.9)”. OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 11: “For the remaining pairs $(a, b) = 1$. Their two equations in (3.8) are equivalent to $t = bmn - ars = b - a$. (3.10)”.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 65, proof of Lemma 10.2, (10.9) for the coprime minor-arc part ([21] Prop. 4.1, §§3.2–4.9)

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMinorSquare

namespace ArtinPrimitiveRoots

open Real

theorem minor_square_bound (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
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
            ‖minorSquare x a A₀ Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-A)) := by
  sorry

end ArtinPrimitiveRoots
