-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_lemma_19
-- name    : BallPolyApprox.VertexBudget.lemma_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:55:25.274803+00:00
-- url     : https://prove2.me/theorems/037fc2cc-1348-4f66-ab8d-ef2bddba4186
-- title:
--   Lemma 19 — concentration of $L=-\log(1-H)$ at its mode and the small-$H$ estimate (47)–(48)
-- statement:
--   Under the standing assumptions of §5.3.1 ($d$ sufficiently large, $M\ge2d$), let $H$ have density proportional to $(1-t)^{d(d-1)/2-1}G_d(t)^{M-d}$ on $(0,1)$, $L=-\log(1-H)$, $L_0$ its mode and $t_0=1-e^{-L_0}$ (the root of (40)). For $t_0\ge d^{-1/2}$, $v>0$, and absolute constants $c,C>0$,
--   $$\mathbb P(L<L_0-v)\le Ce^{-cd^3v^2},$$
--   $$\mathbb E(L-L_0)_++\mathbb E\big[(L_0-L)_+e^{(L_0-L)_+}\big]\le Cd^{-3/2},\qquad \mathbb E|H-t_0|\le C(1-t_0)d^{-3/2}\quad(47).$$
--   Moreover, for every $s\in[t_0,1]$,
--   $$\mathbb P(H<t_0/2)+\mathbb E\big[(s/H)^{d/2}\mathbf 1\{H<t_0/2\}\big]\le\frac{C(1-t_0)}{\sqrt d}\quad(48).$$
--
--   Differences from the source:
--   - encoding: §5.3.1 standing assumption: d sufficiently large, M ≥ 2d → ∃ d0, ∀ d ≥ d0, ∀ M ≥ 2d; reason: the subsection's standing assumption written as hypotheses; it changes no instance the source covers
--   - encoding: H, L, L_0, t_0 from the boundary law of Lemma 16 → H distributed as lawH d M (the explicit density), L = −log(1 − H), t_0 = modeT0 d M, L_0 = −log(1 − t_0); reason: these quantities depend on (d, M) only through the density of H stated in Lemma 16
--   - encoding: expectations and probabilities in ℝ → lower Lebesgue integrals and measures in [0, ∞] compared with ENNReal.ofReal of the bounds; reason: all integrands are nonnegative; this keeps a non-integrable integrand from silently becoming 0
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Lemma 19, p. 18 (PDF 20)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_RandomPolytope

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- Lemma 19 (p. 18, PDF 20), under the standing assumptions of §5.3.1 (`d` sufficiently large,
`M ≥ 2d`): for `H` with density proportional to `(1 − t)^{d(d−1)/2−1} G_d(t)^{M−d}` on `(0, 1)`,
`L = −log(1 − H)`, its mode `L_0` and `t_0 = 1 − e^{−L_0}`, if `t_0 ≥ d^{−1/2}` then, for absolute
constants `c, C > 0` and all `v > 0`: `P(L < L_0 − v) ≤ C e^{−c d³ v²}`;
`E(L − L_0)_+ + E[(L_0 − L)_+ e^{(L_0 − L)_+}] ≤ C d^{−3/2}`; `E|H − t_0| ≤ C (1 − t_0) d^{−3/2}` (47);
and for every `s ∈ [t_0, 1]`, `P(H < t_0/2) + E[(s/H)^{d/2} 1{H < t_0/2}] ≤ C (1 − t_0)/√d` (48). -/
theorem lemma_19 :
    ∃ d0 : ℕ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ d : ℕ, d0 ≤ d → ∀ M : ℕ, 2 * d ≤ M →
      (d : ℝ) ^ (-(1 : ℝ) / 2) ≤ modeT0 d M →
      (∀ v : ℝ, 0 < v →
        lawH d M {t : ℝ | logHeight t < modeL0 d M - v} ≤
          ENNReal.ofReal (C * Real.exp (-(c * (d : ℝ) ^ 3 * v ^ 2)))) ∧
      (∫⁻ t, ENNReal.ofReal (max (logHeight t - modeL0 d M) 0) ∂lawH d M +
          ∫⁻ t, ENNReal.ofReal (max (modeL0 d M - logHeight t) 0 *
            Real.exp (max (modeL0 d M - logHeight t) 0)) ∂lawH d M ≤
        ENNReal.ofReal (C * (d : ℝ) ^ (-(3 : ℝ) / 2))) ∧
      (∫⁻ t, ENNReal.ofReal |t - modeT0 d M| ∂lawH d M ≤
        ENNReal.ofReal (C * (1 - modeT0 d M) * (d : ℝ) ^ (-(3 : ℝ) / 2))) ∧
      (∀ s : ℝ, modeT0 d M ≤ s → s ≤ 1 →
        lawH d M {t : ℝ | t < modeT0 d M / 2} +
            ∫⁻ t in {t : ℝ | t < modeT0 d M / 2}, ENNReal.ofReal ((s / t) ^ ((d : ℝ) / 2)) ∂lawH d M ≤
          ENNReal.ofReal (C * (1 - modeT0 d M) / Real.sqrt d)) := by sorry

end BallPolyApprox.VertexBudget
