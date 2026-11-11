-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_10
-- name    : DPCutRelease.Main.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:12:46.833343+00:00
-- url     : https://prove2.me/theorems/55dfb0af-8c95-4d9f-b236-fc1ea459a9f7
-- title:
--   Lemma 10 — the averaged Gaussian estimator ĝ is within [q_e(X)/4, q_e(X)] on all pairs w.p. 1 − min(β_χ, δ₁)
-- statement:
--   There is a universal constant $C>0$ such that the following holds. For every $X\in\mathcal X$ and $\beta_\chi,\delta_1\in(0,1)$, choose independent random vectors $Z^{(j)}\sim N(0,X)$, $j=1,\dots,k$, set $g(u,v)=\frac1k\sum_{j=1}^k\frac{(Z^{(j)}_u-Z^{(j)}_v)^2}4$ and $\hat g(u,v)=\min\{g(u,v)/2,1\}$. If $k\ge C\log(n/(\beta_\chi\delta_1))$, then with probability at least $1-\min(\beta_\chi,\delta_1)$, simultaneously for every pair $e=\{u,v\}$,
--   $$\frac{q_e(X)}4\le\hat g(u,v)\le q_e(X).$$
--   It makes the clipped Gaussian estimate a constant-factor estimate of the gradient $q(X_D)$ of $F$.
--
--   **Formalization Note.** `batchLaw k X`, `ghat`, `qe` (SDP module).
--
--   Differences from the source:
--   - reading: "For some universal constant C > 0, if k ≥ C log(n/(β_χδ₁))" → ∃ C > 0 quantified before n, X, β_χ, δ₁, k; reason: the constant is universal
--   - encoding: with probability at least 1 − p → the noise/tape measure of the failure set is at most p (outer measure if the set were not measurable); reason: same statement for measurable events; cannot be made vacuous by non-measurability
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 15, Lemma 10 (proof in Appendix B)

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP

open MeasureTheory ProbabilityTheory Matrix

namespace DPCutRelease.Main

/-- Lemma 10 (p. 15): there is a universal `C` such that for every `X ∈ 𝒳`, `β_χ, δ₁ ∈ (0, 1)` and
`k ≥ C log(n/(β_χ δ₁))`, with probability at least `1 − min(β_χ, δ₁)` over `k` i.i.d. `N(0, X)`
vectors, `q_e(X)/4 ≤ ĝ(e) ≤ q_e(X)` for every pair `e` simultaneously. -/
theorem lemma_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (X : Mat n) (βχ δ1 : ℝ) (k : ℕ), X ∈ Elliptope n →
      0 < βχ → βχ < 1 → 0 < δ1 → δ1 < 1 → C * Real.log (n / (βχ * δ1)) ≤ k →
      batchLaw k X {Z | ¬ ∀ e, qe X e / 4 ≤ ghat Z e ∧ ghat Z e ≤ qe X e}
        ≤ ENNReal.ofReal (min βχ δ1) := by sorry

end DPCutRelease.Main
