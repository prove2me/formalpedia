-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_intermediate_frequency
-- name    : BrickworkPorterThomas.Convergence.intermediate_frequency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:15:21.903434+00:00
-- url     : https://prove2.me/theorems/278571bd-5c60-4041-b800-bdc1a1dad1c5
-- title:
--   Lemma 4.3 — intermediate-frequency Fourier mass $\le d\,e^{-\Omega(kh^2)}/h$
-- statement:
--   There are constants $\gamma>0$ and $c>0$ with the following property. Let $f,g$ be probability densities supported in $[0,1]$ that are $C^1$ on $(0,1)$ and continuous on $[0,1]$, with moments $m_j,m'_j$, and put $\hat z=\hat f-\hat g$. Let $k\ge1$, $0<\varepsilon\le d^{-k}$ and $d\ge2$, and suppose that $|m_j-m'_j|\le\varepsilon$ for $0\le j\le k$ and $m_j\le j!/d^j$ for $1\le j\le k$. Then for every $h$ with $\sqrt{\gamma/k}\le h\le1$,
--
--   $$
--   \int_{d/2\le|t|\le d/h}|\hat z(t)|^2\,dt\le\frac{d\,e^{-c\,kh^2}}{h} .
--   $$
--
--   This bounds the Fourier mass in the gap between the low-frequency range of Lemma 4.1 and the band limit given by Theorem 5.1.
--
--   **Formalization Note** $e^{\Omega(-kh^2)}$ is read as $e^{-ckh^2}$ for one constant $c>0$, chosen together with $\gamma$ before all data. A multiplicative prefactor can be absorbed by enlarging $\gamma$ and decreasing $c$, because $kh^2\ge\gamma$. The Fourier mass is a $[0,\infty]$-valued integral.
--
--   Differences from the source:
--
--   - generalization: d = 2^n (standing notation of §2), d ≥ 2 → d any real number with d ≥ 2; reason: the proof uses only real-variable estimates in d; the source instance d = 2^n is a special case
--   - encoding: d e^{Ω(−kh²)}/h for √(γ/k) ≤ h ≤ 1, for some constant γ > 0 → ∃ γ > 0, c > 0 before all data with bound d e^{−c k h²}/h; reason: meaning of the Ω-notation; a constant prefactor is absorbed since k h² ≥ γ
--   - encoding: k unconstrained → 1 ≤ k; reason: √(γ/k) requires k > 0; excludes only the undefined case
--   - reading: “the first k+1 moments … |m_j − m′_j| ≤ ε, and m_j ≤ j!/d^j, for 1 ≤ j ≤ k” → closeness for 0 ≤ j ≤ k, bound m_j ≤ j!/d^j for 1 ≤ j ≤ k; reason: “first k+1 moments” indexes 0..k; at j = 0 both conditions hold for every pair of densities, so the readings agree
--   - encoding: Fourier energy written as an integral of |ẑ|² → the nonnegative extended integral ∫⁻ |ẑ|ₑ² and the finite bound embedded in [0,∞]; reason: preserves possible infinite energy before the estimate; the conclusion asserts finiteness rather than using a Bochner integral that defaults to zero
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §4, p. 11, Lemma 4.3, Eqs. (54)–(55); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Densities

namespace BrickworkPorterThomas.Convergence

open MeasureTheory

/-- Lemma 4.3 (p. 11). There are constants `γ > 0` and `c > 0` such that: if `f, g` are
probability densities supported in `[0,1]`, `C¹` on `(0,1)` and continuous on `[0,1]`, whose
moments satisfy `|m_j − m'_j| ≤ ε` (`0 ≤ j ≤ k`) and `m_j ≤ j!/d^j` (`1 ≤ j ≤ k`) with
`0 < ε ≤ d^{-k}` and `d ≥ 2`, then for every `√(γ/k) ≤ h ≤ 1`,
`∫_{d/2 ≤ |t| ≤ d/h} |ẑ(t)|² dt ≤ d e^{-c k h²} / h` (`ẑ = f̂ − ĝ`). -/
theorem intermediate_frequency : ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
    ∀ (f g : ℝ → ℝ) (k : ℕ) (d ε h : ℝ),
      IsDensity f → IsDensity g → SupportedInUnit f → SupportedInUnit g →
      ContDiffOn ℝ 1 f (Set.Ioo 0 1) → ContinuousOn f (Set.Icc 0 1) →
      ContDiffOn ℝ 1 g (Set.Ioo 0 1) → ContinuousOn g (Set.Icc 0 1) → 1 ≤ k →
      (∀ j ≤ k, |moment f j - moment g j| ≤ ε) →
      (∀ j, 1 ≤ j → j ≤ k → moment f j ≤ (j.factorial : ℝ) / d ^ j) →
      0 < ε → ε ≤ (d ^ k)⁻¹ → 2 ≤ d →
      Real.sqrt (γ / k) ≤ h → h ≤ 1 →
      ∫⁻ t in {t : ℝ | d / 2 ≤ |t| ∧ |t| ≤ d / h},
          ‖charDensity f t - charDensity g t‖ₑ ^ 2 ≤
        ENNReal.ofReal (d * Real.exp (-(c * k * h ^ 2)) / h) := by sorry

end BrickworkPorterThomas.Convergence
