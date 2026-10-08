-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_mass_conditioned_on_divisor
-- name    : ArtinPrimitiveRoots.mass_conditioned_on_divisor
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:27:23.222458+00:00
-- url     : https://prove2.me/theorems/7dc37e74-ae42-4da6-a549-d5acffae454e
-- title:
--   Lemma 12.4 (OpenAI) — mass conditioned on a prime divisor
-- statement:
--   Let $M, c, u$ satisfy (12.1), let $\Psi$ be $C^\infty$ with closed support in $(1, 2)$, $0 \le \Psi \le 1$ and $\int\Psi > 0$, and let $K \ge 1$ and $0.1 < a_1 < \cdots < a_K < 0.2$. Let $0 < \kappa < 0.01$, $0 < b < 0.01$, and $b \le \gamma < \gamma' \le 1/2 - \kappa$. Write $W = $ `sieveLevel x`, $V = $ `mertensProduct`, $w = $ `constructionWeight M c u Ψ x a`, $X_0 = $ `totalMass M c u Ψ x a` and $\mathfrak S_M = $ `singularSeries M`. Then for every $\eta > 0$ there is $x_0$ such that for $x \ge x_0$,
--
--   $$\Bigl|\sum_{x^\gamma < n \le x^{\gamma'},\ n \text{ prime}}\ \sum_{n \mid d,\ P^-(d) > W} w(d) \;-\; \mathfrak S_M X_0 V(W)\log\frac{\gamma'}{\gamma}\Bigr| \le \eta\,\mathfrak S_M X_0 V(W).$$
--
--   **Formalization note.** The $o(1)$ of (12.23) is written as an error at most $\eta\,\mathfrak S_M X_0 V(W)$ for $x \ge x_0(\eta)$. Of the standing assumptions (12.11), $0 < \kappa < 0.01$ and $0 < b < 0.01$ are included; $\varepsilon$ does not occur in the statement and is omitted.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 79: “Lemma 12.4 (Mass conditioned on a divisor). For any fixed $b \le \gamma < \gamma' \le 1/2 - \kappa$, $\sum_{x^\gamma < n \le x^{\gamma'},\ n \text{ prime}}\ \sum_{n \mid d,\ P^-(d) > W} w(d) = \mathfrak S_M X_0 V(W)\Bigl(\log\frac{\gamma'}{\gamma} + o(1)\Bigr)$. (12.23)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 79, Lemma 12.4

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem mass_conditioned_on_divisor (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M)
    (hc : c = 2 ∨ c = 4) (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1)
    (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y)
    (K : ℕ) (hK : 1 ≤ K) (a : Fin K → ℝ) (ha : StrictMono a)
    (ha' : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2)
    (κ b : ℝ) (hκ : 0 < κ) (hκ' : κ < 0.01) (hb : 0 < b) (hb' : b < 0.01)
    (γ γ' : ℝ) (hbγ : b ≤ γ) (hγγ' : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ) :
    ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
          ∑' d : ℕ, (if n ∣ d ∧ IsRough (sieveLevel x) d then
            constructionWeight M c u Ψ x a d else 0) -
        singularSeries M * totalMass M c u Ψ x a * mertensProduct (sieveLevel x) *
          log (γ' / γ)| ≤
      η * (singularSeries M * totalMass M c u Ψ x a * mertensProduct (sieveLevel x)) := by
  sorry

end ArtinPrimitiveRoots
