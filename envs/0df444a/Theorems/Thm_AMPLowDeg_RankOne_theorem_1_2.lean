-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_theorem_1_2
-- name    : AMPLowDeg.RankOne.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:01:31.501448+00:00
-- url     : https://prove2.me/theorems/c0a276f7-cff1-4036-804a-d57666e24ec5
-- title:
--   Theorem 1.2 — growing-degree polynomials cannot beat Bayes AMP
-- statement:
--   Let $\pi$ be a prior on $\mathbb R$ with $\mathbb E[\Theta]\ne0$ that is sub-Gaussian with moment parameter $K$: $K\ge1$ and $\|\Theta\|_p\le K\sqrt p$ for every integer $p\ge2$. Consider model (1.1), $Y=n^{-1/2}\theta\theta^\top+W$ with $\theta_i$ i.i.d. $\pi$ and unit-variance Gaussian noise (diagonal included), the low-degree MMSE (1.6) and $q_{\mathrm{AMP}}$ of (1.3).
--
--   1. For every constant $C_0\ge60$ and all integers $n\ge1$, $D\ge1$,
--   $$
--   \mathrm{MMSE}_{\le D}\ \ge\ m_2-q_{\mathrm{AMP}}-\sum_{g=1}^{D}\left(\frac{[2C_0K(D+1)]^{C_0}}{n}\right)^{g}.
--   $$
--   2. If in addition $[2C_0K(D+1)]^{C_0}\le n/2$, the error term is at most $2[2C_0K(D+1)]^{C_0}/n$.
--   3. For every sequence of degrees $D(n)=o(n^{1/60})$,
--   $$
--   \liminf_{n\to\infty}\mathrm{MMSE}_{\le D(n)}\ \ge\ m_2-q_{\mathrm{AMP}}.
--   $$
--
--   Since Bayes AMP achieves the error $m_2-q_{\mathrm{AMP}}$, no polynomial estimator of degree up to $n^{1/60-\varepsilon}$ does asymptotically better than AMP in the rank-one spiked model.
--
--   **Formalization Note** $\mathrm{MMSE}_{\le D}$ is valued in $[0,\infty]$ (a lower Lebesgue integral and an infimum there), so the bounds are written as $\mathrm{ofReal}(\cdot)\le\mathrm{MMSE}_{\le D}$ and the lim inf is taken in $[0,\infty]$. The norms $\|\Theta\|_p$ are Mathlib's `eLpNorm`, so the moment hypothesis also asserts their finiteness. $[2C_0K(D+1)]^{C_0}$ is a real power.
--
--   Differences from the source:
--
--   - generalization: K = max{1, sup_{p ≥ 2} ‖Θ‖_p/√p} < ∞ (sup over real p) → any real K ≥ 1 with ‖Θ‖_p ≤ K√p for every integer p ≥ 2; reason: the paper's K is such a K, so the statement specializes to the source; the proof only uses p = 4D + 2
--   - generalization: degree sequences D(n) (integers ≥ 1) with D(n) = o(n^{1/60}) → every D : ℕ → ℕ with D(n) = o(n^{1/60}), D(n) = 0 allowed; reason: every sequence of the source is allowed; MMSE_{≤D} is nonincreasing in D
--   - encoding: C₀ = 60 (or any larger constant) → ∀ real C₀ ≥ 60, with the real power [2C₀K(D+1)]^{C₀}; reason: this is the source's quantification of the constant
--   - encoding: standing assumption E|Θ|^p < ∞ for all p → not stated separately; reason: implied by the moment hypothesis ‖Θ‖_p ≤ K√p < ∞, which is stated with eLpNorm in [0, ∞]
--   - encoding: lim inf_{n→∞} MMSE_{≤D(n)} ≥ m₂ − q_AMP (real lim inf) → ENNReal.ofReal (m₂ − q_AMP) ≤ liminf of mmseLD π n (D n) in [0, ∞]; reason: MMSE_{≤D} is finite and nonnegative, so the real and the [0, ∞] lim inf agree; no boundedness side condition is needed in [0, ∞]
--   - encoding: MMSE_{≤D} ≥ x with MMSE_{≤D} a real infimum → ENNReal.ofReal x ≤ mmseLD π n D, the risk being a lower Lebesgue integral in [0, ∞]; reason: MMSE_{≤D} is finite (the zero estimator has risk m₂), so for a finite value both forms say the same; no integrability convention is involved
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 4, Theorem 1.2 (1.7) and the two sentences after it; proof p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Potential

open MeasureTheory ProbabilityTheory Filter Asymptotics

namespace AMPLowDeg.RankOne

/-- Theorem 1.2, p. 4 — low-degree polynomials cannot beat Bayes AMP at growing degree.
Let `π` be a prior with `E[Θ] ≠ 0` and sub-Gaussian moment parameter `K`
(`K ≥ 1`, `‖Θ‖_p ≤ K √p` for every integer `p ≥ 2`). Then
(a) for every constant `C₀ ≥ 60` and all integers `n, D ≥ 1`,
`MMSE_{≤D} ≥ m₂ − q_AMP − Σ_{g=1}^{D} ([2C₀K(D+1)]^{C₀} / n)^g`;
(b) if moreover `[2C₀K(D+1)]^{C₀} ≤ n/2`, the error term is at most `2[2C₀K(D+1)]^{C₀}/n`;
(c) for every `D(n) = o(n^{1/60})`, `liminf_{n→∞} MMSE_{≤D(n)} ≥ m₂ − q_AMP`. -/
theorem theorem_1_2 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (K : ℝ) (hK1 : 1 ≤ K)
    (hK : ∀ p : ℕ, 2 ≤ p → eLpNorm (fun x : ℝ => x) (p : ENNReal) π ≤
      ENNReal.ofReal (K * Real.sqrt p)) :
    (∀ C₀ : ℝ, 60 ≤ C₀ → ∀ n D : ℕ, 1 ≤ n → 1 ≤ D →
      ENNReal.ofReal (m2 π - qAMP π -
          ∑ g ∈ Finset.Icc 1 D, ((2 * C₀ * K * ((D : ℝ) + 1)) ^ C₀ / n) ^ g) ≤
        mmseLD π n D) ∧
    (∀ C₀ : ℝ, 60 ≤ C₀ → ∀ n D : ℕ, 1 ≤ n → 1 ≤ D →
      (2 * C₀ * K * ((D : ℝ) + 1)) ^ C₀ ≤ (n : ℝ) / 2 →
      ∑ g ∈ Finset.Icc 1 D, ((2 * C₀ * K * ((D : ℝ) + 1)) ^ C₀ / n) ^ g ≤
        2 * (2 * C₀ * K * ((D : ℝ) + 1)) ^ C₀ / n) ∧
    (∀ D : ℕ → ℕ, (fun n : ℕ => (D n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 60)) →
      ENNReal.ofReal (m2 π - qAMP π) ≤ liminf (fun n : ℕ => mmseLD π n (D n)) atTop) := by sorry

end AMPLowDeg.RankOne
