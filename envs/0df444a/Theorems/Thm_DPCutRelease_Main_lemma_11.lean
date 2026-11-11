-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_11
-- name    : DPCutRelease.Main.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:12:51.645274+00:00
-- url     : https://prove2.me/theorems/383c0cfe-88ef-4e8a-926e-a0aa928974c0
-- title:
--   Lemma 11 — conditionally on Lemma 10's event, ⟨D, ĝ⟩ ≥ (1/2)Σ D_e q_e(X) with probability at least c₀
-- statement:
--   There are universal constants $C,c_0>0$ such that the following holds. For every $D\in\mathbb R^{\binom n2}$, $X\in\mathcal X$ and $\beta_\chi,\delta_1\in(0,1)$, with $Z^{(1)},\dots,Z^{(k)}$, $g$ and $\hat g$ as in Lemma 10 and $k\ge C\log(n/(\beta_\chi\delta_1))$, conditioning on the good event of Lemma 10 ($q_e(X)/4\le\hat g(e)\le q_e(X)$ for all $e$),
--   $$\Pr\Big[\langle D,\hat g\rangle\ge\frac12\sum_{e=\{u,v\}}D_{uv}\,q_e(X)\Big]\ge c_0 .$$
--   It gives each trial of Algorithm 2 a constant success probability when $F(D)$ is large (Lemma 20).
--
--   **Formalization Note.** The conditional probability is `ProbabilityTheory.cond` of `batchLaw k X` on the good event.
--
--   Differences from the source:
--   - reading: "For some universal constant C > 0 … for a universal constant c₀ > 0" → ∃ C c₀ > 0 quantified before n, D, X, β_χ, δ₁, k; reason: the constants are universal
--   - encoding: conditional probability given the good event of Lemma 10 → ProbabilityTheory.cond (batchLaw k X) good; reason: Lean’s conditional measure; the good event has positive probability for C large (Lemma 10)
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 16, Lemma 11 (proof in Appendix B)

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP

open MeasureTheory ProbabilityTheory Matrix

namespace DPCutRelease.Main

/-- Lemma 11 (p. 16): there are universal `C, c₀ > 0` such that for every `D`, `X ∈ 𝒳`,
`β_χ, δ₁ ∈ (0, 1)` and `k ≥ C log(n/(β_χ δ₁))`, conditionally on the good event of Lemma 10,
`Pr[⟨D, ĝ⟩ ≥ (1/2) Σ_e D_e q_e(X)] ≥ c₀`. -/
theorem lemma_11 :
    ∃ C c0 : ℝ, 0 < C ∧ 0 < c0 ∧ ∀ (n : ℕ) (D : EdgeVec n) (X : Mat n) (βχ δ1 : ℝ) (k : ℕ),
      X ∈ Elliptope n → 0 < βχ → βχ < 1 → 0 < δ1 → δ1 < 1 → C * Real.log (n / (βχ * δ1)) ≤ k →
      ENNReal.ofReal c0 ≤
        cond (batchLaw k X) {Z | ∀ e, qe X e / 4 ≤ ghat Z e ∧ ghat Z e ≤ qe X e}
          {Z | 1 / 2 * ∑ e, D e * qe X e ≤ dot D (ghat Z)} := by sorry

end DPCutRelease.Main
