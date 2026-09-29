-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification
-- name    : AvramDividend.Classical.local_verification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:59:32.351633+00:00
-- url     : https://prove2.me/theorems/f318a688-56f8-459d-865b-f64d192f9630
-- title:
--   Proposition 4(i) — local verification theorem for the classical dividend problem
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions, with generator $\Gamma$, and let $q>0$. Let $C\in(0,\infty]$ and let $w:\mathbb R\to\mathbb R$ be continuous on $[0,\infty)$ with $w(0)\ge0$ and $w(x)=0$ for $x<0$. Suppose that $w$ is $C^2$ on $(0,C)$ if $X$ has unbounded variation, and $C^1$ on $(0,C)$ if $X$ has bounded variation, and that $w$ satisfies the variational inequality (5.8) on $(0,C)$:
--   $$\max\{\Gamma w(x)-qw(x),\;1-w'(x)\}=0,\qquad x\in(0,C).$$
--   Then
--   $$w(x)\ge\sup_{\pi\in\Pi_{\le C}}v_\pi(x)\qquad\text{for all }x\in[0,C]\cap[0,\infty),$$
--   and in particular, if $C=\infty$, then $w(x)\ge v_*(x)$ for all $x\ge0$.
--
--   This is the verification step: any sufficiently smooth solution of (5.8) dominates the value of every strategy that keeps the reserves below $C$.
--
--   **Formalization Note.** The paper states $w\ge\sup_{\pi\in\Pi_{\le C}}v_\pi$ on all of $[0,\infty)$. For finite $C$ this cannot hold beyond $C$, because nothing constrains $w$ on $(C,\infty)$ while a strategy in $\Pi_{\le C}$ started at $x>C$ first pays out at least $x-C$; the proof applies Itô's formula to $w(U)$ with $U\le C$. The conclusion is therefore stated for initial capital $x\le C$, which is all of $[0,\infty)$ when $C=\infty$. "$w(0)=w(0+)$" is continuity of $w$ on $[0,\infty)$. The hypothesis (5.8) includes that the jump integral of $\Gamma w(x)$ converges; for $x\in(0,C)$ this holds for every $w$ satisfying the smoothness assumptions, so it only rules out reading a divergent integral as $0$.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 18, Proposition 4(i); variational inequality (5.8) on p. 17

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem local_verification {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
      (C = ⊤ → ∀ x : ℝ, 0 ≤ x → valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry

end AvramDividend.Classical
