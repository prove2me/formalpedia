-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_truncated_laplace
-- name    : BrickworkPorterThomas.Convergence.truncated_laplace
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:15:10.946855+00:00
-- url     : https://prove2.me/theorems/057106e4-5f3c-4406-a9f7-e8ac4ff04c84
-- title:
--   Lemma A.1 — truncated Laplace transform bound $|H(s)|\le2^{-c_0k}$ for $|s|\le d/8$
-- statement:
--   There is a constant $c_0>0$ with the following property. Let $f,g$ be probability densities supported in $[0,1]$ with moments $m_j,m'_j$ satisfying
--
--   $$
--   |m_j-m'_j|\le\varepsilon,\qquad m_j\le\frac{j!}{d^j}\qquad(0\le j\le k),
--   $$
--
--   where $0<\varepsilon\le d^{-k}$, $d\ge2$ and $k\ge2$. Let $L=2k/d$ and $H(s)=\int_{-L}^{L}(f(x)-g(x))e^{-sx}\,dx$. Then for every complex $s$ with $|s|\le d/8$,
--
--   $$
--   |H(s)|\le2^{-c_0k} .
--   $$
--
--   This is the inner-circle estimate fed into the Hadamard three-circle theorem in the proof of Lemma 4.3.
--
--   **Formalization Note** $c_0$ is uniform in $f,g,k,d,\varepsilon$ and $s$.
--
--   Differences from the source:
--
--   - generalization: d = 2^n (standing notation of §2), d ≥ 2 → d any real number with d ≥ 2; reason: the proof uses only real-variable estimates in d; the source instance d = 2^n is a special case
--   - encoding: “there exists a constant c₀ > 0 such that, for k ≥ 2 and any s” → ∃ c₀ > 0 before f, g, k, d, ε, s; reason: the constant is absolute (the proof gives 0 < c₀ ≤ 1/4)
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), Appendix A, p. 22, Lemma A.1, Eqs. (155)–(156); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Densities

namespace BrickworkPorterThomas.Convergence

/-- Lemma A.1 (p. 22). There is a constant `c₀ > 0` such that: if `f, g` are probability densities
supported in `[0,1]` whose moments satisfy `|m_j − m'_j| ≤ ε` and `m_j ≤ j!/d^j` for `0 ≤ j ≤ k`,
with `0 < ε ≤ d^{-k}`, `d ≥ 2` and `k ≥ 2`, then with `L = 2k/d` and
`H(s) = ∫_{-L}^{L} (f(x) − g(x)) e^{-sx} dx`, `|H(s)| ≤ 2^{-c₀ k}` for every complex `|s| ≤ d/8`. -/
theorem truncated_laplace : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (f g : ℝ → ℝ) (k : ℕ) (d ε : ℝ),
      IsDensity f → IsDensity g → SupportedInUnit f → SupportedInUnit g →
      (∀ j ≤ k, |moment f j - moment g j| ≤ ε) →
      (∀ j ≤ k, moment f j ≤ (j.factorial : ℝ) / d ^ j) →
      0 < ε → ε ≤ (d ^ k)⁻¹ → 2 ≤ d → 2 ≤ k →
      ∀ s : ℂ, ‖s‖ ≤ d / 8 →
        ‖truncLaplace f g (2 * k / d) s‖ ≤ (2 : ℝ) ^ (-(c₀ * k)) := by sorry

end BrickworkPorterThomas.Convergence
