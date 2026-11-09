-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_low_frequency
-- name    : BrickworkPorterThomas.Convergence.low_frequency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:15:04.915632+00:00
-- url     : https://prove2.me/theorems/b83a7ea6-9190-438e-9632-aa3d37457ed7
-- title:
--   Lemma 4.1 — low-frequency Fourier mass from matched moments
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $f,g$ be probability densities supported in $[0,1]$, with moments $m_j=\int x^jf$ and $m'_j=\int x^jg$, and put $\hat z=\hat f-\hat g$. Let $k\ge1$, $0<\varepsilon\le d^{-k}$ and $d\ge4k$, and suppose that for $0\le j\le k$
--
--   $$
--   |m_j-m'_j|\le\varepsilon,\qquad m_j\le\frac{j!}{d^j}.
--   $$
--
--   Then
--
--   $$
--   \int_{|t|\le d/2}|\hat z(t)|^2\,dt\le C\,\frac{d}{k\,2^{2k}} .
--   $$
--
--   This bounds the low-frequency part of the Fourier integral in Theorem 2.8 using only the first $k+1$ moments. In the application $f$ is the Haar output density, whose moments satisfy $m_j\le j!/d^j$, and $g$ is the circuit density.
--
--   **Formalization Note** The source's $O(\cdot)$ is a single existential constant chosen before all data. The Fourier mass is a $[0,\infty]$-valued integral.
--
--   Differences from the source:
--
--   - generalization: d = 2^n (standing notation of §2), d ≥ 4k → d any real number with d ≥ 4k; reason: the proof uses only real-variable estimates in d; the source instance d = 2^n is a special case
--   - encoding: O(d/(k 2^{2k})) → ∃ C > 0 before f, g, k, d, ε with bound C d/(k 2^{2k}); reason: uniform constant of the O-notation
--   - encoding: k unconstrained (design order, k ≥ 2 in the application) → 1 ≤ k; reason: k = 0 makes d/(k 2^{2k}) a division by zero; excludes only the undefined case
--   - encoding: Fourier energy written as an integral of |ẑ|² → the nonnegative extended integral ∫⁻ |ẑ|ₑ² and the finite bound embedded in [0,∞]; reason: preserves possible infinite energy before the estimate; the conclusion asserts finiteness rather than using a Bochner integral that defaults to zero
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §4, p. 9, Lemma 4.1, Eqs. (38)–(39); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Densities

namespace BrickworkPorterThomas.Convergence

open MeasureTheory

/-- Lemma 4.1 (p. 9). There is an absolute constant `C > 0` such that: if `f, g` are probability
densities supported in `[0,1]` whose moments satisfy `|m_j − m'_j| ≤ ε` and `m_j ≤ j!/d^j` for
`0 ≤ j ≤ k` (`m_j` the moments of `f`, `m'_j` those of `g`), with `0 < ε ≤ d^{-k}` and `d ≥ 4k`,
then `∫_{|t| ≤ d/2} |ẑ(t)|² dt ≤ C d / (k 2^{2k})`, where `ẑ = f̂ − ĝ`. -/
theorem low_frequency : ∃ C : ℝ, 0 < C ∧
    ∀ (f g : ℝ → ℝ) (k : ℕ) (d ε : ℝ),
      IsDensity f → IsDensity g → SupportedInUnit f → SupportedInUnit g → 1 ≤ k →
      (∀ j ≤ k, |moment f j - moment g j| ≤ ε) →
      (∀ j ≤ k, moment f j ≤ (j.factorial : ℝ) / d ^ j) →
      0 < ε → ε ≤ (d ^ k)⁻¹ → 4 * (k : ℝ) ≤ d →
      ∫⁻ t in Set.Icc (-(d / 2)) (d / 2), ‖charDensity f t - charDensity g t‖ₑ ^ 2 ≤
        ENNReal.ofReal (C * d / (k * 2 ^ (2 * k))) := by sorry

end BrickworkPorterThomas.Convergence
