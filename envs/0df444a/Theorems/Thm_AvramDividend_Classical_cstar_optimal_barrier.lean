-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier
-- name    : AvramDividend.Classical.cstar_optimal_barrier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:58:02.419039+00:00
-- url     : https://prove2.me/theorems/00fcfc56-8ba9-4464-b9ee-c1b9e3af1ecd
-- title:
--   Proposition 3(i) — $\pi_{c^*}$ is the best barrier strategy for initial capital in $[0,c^*]$
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions, let $q>0$ and let $W=W^{(q)}$ be its $q$-scale function. Then $c^*<\infty$, and the barrier at $c^*$ is optimal among all barrier strategies for initial capital in $[0,c^*]$:
--   $$v_a(x)\le v_{c^*}(x)\qquad\text{for all }x\in[0,c^*]\text{ and all }a\ge0,$$
--   where $v_a$ is the barrier value function (5.1) ($v_a(x)=W(x)/W'(a)$ for $0\le x\le a$, $v_a(x)=x-a+W(a)/W'(a)$ for $x>a$, and $v_0(x)=x+W(0)/W'(0+)$).
--
--   This is the first step of the proof of Theorem 2: it identifies $c^*$ as the best barrier level before optimality over all strategies is addressed.
--
--   **Formalization Note.** $v_{c^*}$ is the barrier value function at the real number $c^*$, which is meaningful because $c^*<\infty$ is part of the conclusion.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 15, Proposition 3(i)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem cstar_optimal_barrier {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by sorry

end AvramDividend.Classical
