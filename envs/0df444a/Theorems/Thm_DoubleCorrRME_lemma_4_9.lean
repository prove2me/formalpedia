-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_4_9
-- name    : DoubleCorrRME.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:10.677506+00:00
-- url     : https://prove2.me/theorems/9121d2b9-066e-49a8-ab29-7f0de0a395df
-- title:
--   Lemma 4.9 ([PP25, Prop. 8]), p.28 — first-moment to second-moment truncation: $|I|\ge(1-\gamma)N$, $O(\rho^2/\gamma)$
-- statement:
--   Let $v_1,\dots,v_N\in\mathbb R^d$ ($N\ge1$) satisfy
--
--   $$\sup_{u\in S^{d-1}}\frac1N\sum_{i=1}^N|\langle u,v_i\rangle|\le\rho .$$
--
--   There is an absolute constant $C$ such that for every $\gamma\in(0,\tfrac12)$ there is an index set $I\subseteq[N]$ with $|I|\ge(1-\gamma)N$ and
--
--   $$\sup_{u\in S^{d-1}}\frac1{|I|}\sum_{i\in I}\langle u,v_i\rangle^2\le C\frac{\rho^2}\gamma .$$
--
--   It converts the first-moment bound of Lemma 4.5 into the covariance bound of the second stable reference.
--
--   Differences from the source:
--   - encoding: v_1, …, v_N and 1/N → 1 ≤ N; reason: the average (1/N)∑ requires N ≥ 1
--   - encoding: O(ρ²/γ) → ∃ C > 0 before N, d, v, ρ, γ; reason: meaning of an absolute constant
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 4.9, p.28 (PDF p.29)

import Mathlib
import Definitions.Def_DoubleCorrRME_Model

namespace DoubleCorrRME

/-- **Lemma 4.9** ([PP25, Proposition 8]), p.28 (PDF p.29).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Let v_1, …, v_N ∈ ℝ^d satisfy sup_{u∈S^{d−1}} (1/N)∑_{i=1}^N |⟨u, v_i⟩| ≤ ρ. For all γ ∈ (0, 1/2),
there exists an index set I ⊆ [N] with |I| ≥ (1 − γ)N such that
sup_{u∈S^{d−1}} (1/|I|)∑_{i∈I} |⟨u, v_i⟩|² ≤ O(ρ²/γ)."

**Formalization Note.**
* The constant is chosen before `N, d, v, ρ, γ`. `N ≥ 1`, so `1/N` is meaningful; then
  `|I| ≥ (1 − γ)N > 0`, so `1/|I|` is too.
* Both suprema over the sphere are written as "for every unit `u`". -/
theorem lemma_4_9 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N d : ℕ), 1 ≤ N → ∀ (v : Fin N → Vec d) (ρ : ℝ),
        (∀ u : Vec d, ‖u‖ = 1 → ((N : ℝ))⁻¹ * ∑ i, |inner ℝ u (v i)| ≤ ρ) →
        ∀ γ : ℝ, 0 < γ → γ < 1 / 2 →
          ∃ I : Finset (Fin N), (1 - γ) * (N : ℝ) ≤ I.card ∧
            ∀ u : Vec d, ‖u‖ = 1 →
              ((I.card : ℝ))⁻¹ * ∑ i ∈ I, |inner ℝ u (v i)| ^ 2 ≤ C * (ρ ^ 2 / γ) := by sorry

end DoubleCorrRME
