-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
-- name    : AvramDividend.Classical.generator_vcstar_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:59:55.314146+00:00
-- url     : https://prove2.me/theorems/88d146b8-1b63-463d-8780-cf80ad7a9d40
-- title:
--   Lemma 4 — $(\Gamma v_{c^*}-qv_{c^*})(x)=0$ on $(0,c^*)$
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions, with generator $\Gamma$, let $q>0$ and let $W=W^{(q)}$ be its $q$-scale function. Let $v_{c^*}$ be the candidate value function, extended by $0$ to $(-\infty,0)$. Assume that $\sigma>0$, or that $X$ has bounded variation, or that $v_{c^*}$ is $C^2$ on $(0,c^*)$. If $c^*>0$, then for every $x\in(0,c^*)$ the jump integral of $\Gamma v_{c^*}(x)$ converges and
--   $$(\Gamma v_{c^*}-qv_{c^*})(x)=0 .$$
--
--   Together with Lemma 3(i) this shows that $v_{c^*}$ solves the variational inequality (5.8) on $(0,c^*)$.
--
--   **Formalization Note.** The paper states Lemma 4 without a smoothness proviso; its proof applies Itô's formula, which needs $v_{c^*}\in C^1(0,c^*)$ (bounded variation) or $C^2(0,c^*)$ (unbounded variation). Under (3.3) these hold when $\sigma>0$ or $X$ has bounded variation (p. 14); otherwise the smoothness is assumed, which is the proviso of Theorem 2 restricted to $(0,c^*)$. Convergence of the jump integral is part of the conclusion.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 20, Lemma 4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_vcstar_eq_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x = 0 := by sorry

end AvramDividend.Classical
