-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_cstar_optimal
-- name    : AvramDividend.Classical.barrier_cstar_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:00:39.768793+00:00
-- url     : https://prove2.me/theorems/545c65ef-edd3-4ecb-aeaa-8dd6c5bce0e7
-- title:
--   Theorem 2 — optimality of the barrier strategy at $c^*$ in the classical dividend problem
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions (no monotone paths, $\mathbf E[X_1]>-\infty$, condition (3.3)), with generator $\Gamma$, let $q>0$, and let $W=W^{(q)}$ be its $q$-scale function. Let $c^*$ be the barrier level (5.2), $v_{c^*}$ the barrier value function (5.1) at $c^*$ (extended by $0$ to $(-\infty,0)$), and $\pi_{c^*}$ the barrier strategy at level $c^*$. Assume that $\sigma>0$, or that $X$ has bounded variation, or that $v_{c^*}\in C^2(0,\infty)$. Then $c^*<\infty$ and:
--
--   1. $\pi_{c^*}$ is optimal in $\Pi_{\le c^*}$: for every initial capital $x\ge0$, $\pi_{c^*}\in\Pi_{\le c^*}$, its value is $v_{c^*}(x)$, and
--   $$v_{c^*}(x)=\sup_{\pi\in\Pi_{\le c^*}}v_\pi(x).$$
--   2. If $(\Gamma v_{c^*}-qv_{c^*})(x)\le0$ for all $x>c^*$, then the value function of the classical dividend problem (2.2) is
--   $$v_*(x)=v_{c^*}(x)\qquad(x\ge0),$$
--   and $\pi_*=\pi_{c^*}$ is an optimal strategy (it is admissible and its value is $v_*$).
--
--   The theorem reduces the optimal dividend problem for a general spectrally negative Lévy process to a condition on the scale function: when the generator inequality holds above $c^*$, paying dividends by reflection at $c^*$ is optimal, and the value function is explicit in $W^{(q)}$.
--
--   **Formalization Note.** All values are in $[0,\infty]$ and the identities with $v_{c^*}(x)$ are between these and the (finite, nonnegative) formula, so finiteness is part of the claim. The paper prints "$\pi^*_c$" in (i) for $\pi_{c^*}$. In (ii) the hypothesis includes that the jump integral of $\Gamma v_{c^*}(x)$ converges for $x>c^*$; this always holds there because $v_{c^*}$ is affine with slope $1$ near $x$ and bounded on $(-\infty,x]$, so it only rules out reading a divergent integral as $0$. Conventions for admissibility (non-strict inequality, the lump sum at time $0$) and for (5.2) are those of the definition items.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 14, Theorem 2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_cstar_optimal {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ x : ℝ, (cstar W).toReal < x →
          X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by sorry

end AvramDividend.Classical
