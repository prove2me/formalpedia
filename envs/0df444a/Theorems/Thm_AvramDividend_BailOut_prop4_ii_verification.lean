-- Prove2me | Theorems.Thm_AvramDividend_BailOut_prop4_ii_verification
-- name    : AvramDividend.BailOut.prop4_ii_verification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:08:58.560714+00:00
-- url     : https://prove2.me/theorems/9c097904-980e-4440-b431-027a0cbc81a5
-- title:
--   Proposition 4(ii) — verification theorem for the bail-out problem
-- statement:
--   Let $X$ be a spectrally negative Lévy process with triplet $(c,\sigma,\nu)$ and generator $\Gamma$, satisfying the standing assumptions. Let $q>0$ and $\varphi>1$. Let $w:\mathbb R\to\mathbb R$ satisfy the following:
--
--   1. $w$ is $C^2$ on $[0,\infty)$ and $w(x)=w(0)+\varphi x$ for $x\le0$;
--   2. $w$ is in the domain of $\Gamma$ at every $x>0$: the integrand $y\mapsto w(x+y)-w(x)-w'(x)y\mathbf 1_{\{|y|<1\}}$ is $\nu$-integrable;
--   3. $w$ satisfies the variational inequality (5.9):
--
--   $$\max\{\Gamma w(x)-qw(x),\,1-w'(x)\}=0\quad(x>0),\qquad w'(x)\le\varphi\quad(x>0),\qquad w'(x)=\varphi\quad(x<0).$$
--
--   Then $w\ge\bar v_*$ on $[0,\infty)$, where $\bar v_*$ is the value function of the bail-out problem (2.4).
--
--   This is the upper half of the proof of Theorem 3: applied to $w=\bar v_{d^*}$ it gives $\bar v_*\le\bar v_{d^*}$.
--
--   **Formalization Note** $C^2[0,\infty)$ is `ContDiffOn ℝ 2 w (Set.Ici 0)`, one-sided at $0$. The integrability hypothesis spells out the paper's "$w$ in the domain of $\Gamma$" (p. 17), so that $\Gamma w$ is not a junk value.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 18, Proposition 4(ii), with (5.9) from p. 17

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_BailOutProblem
import Definitions.Def_AvramDividend_BailOut_BarrierCandidates

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem prop4_ii_verification {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q) {φ : ℝ} (hφ : 1 < φ)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 2 w (Set.Ici 0))
    (hext : ∀ x : ℝ, x ≤ 0 → w x = w 0 + φ * x)
    (hdom : ∀ x : ℝ, 0 < x →
      Integrable (fun y => w (x + y) - w x - (if |y| < 1 then deriv w x * y else 0))
        Lv.triplet.ν)
    (hHJB : ∀ x : ℝ, 0 < x → max (generator Lv.triplet w x - q * w x) (1 - deriv w x) = 0)
    (hslope : ∀ x : ℝ, 0 < x → deriv w x ≤ φ)
    (hslope_neg : ∀ x : ℝ, x < 0 → deriv w x = φ) :
    ∀ x : ℝ, 0 ≤ x → optimalValue Lv q φ x ≤ ((w x : ℝ) : EReal) := by sorry

end AvramDividend.BailOut
