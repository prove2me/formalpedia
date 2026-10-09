-- Prove2me | Theorems.Thm_BanKeskin_KnownSparsity_theorem_2
-- name    : BanKeskin.KnownSparsity.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:35.037925+00:00
-- url     : https://prove2.me/theorems/da9d887a-b886-4a0e-afd2-7868c5e920ca
-- title:
--   Theorem 2, p. 5556 — ILSX expected regret at most C s√T log T
-- statement:
--   Consider linear demand with known support $\mathcal S$, $s=|\mathcal S|$, compact parameter rectangle $\Theta_{\mathcal S}$, the stated feature and shock conditions, and the ILSX policy using distinct experimental prices $m_1,m_2$. There is a finite positive constant $C$ such that, for every $\theta_{\mathcal S}\in\Theta_{\mathcal S}$ and every horizon $T\ge2$,
--
--   $$\Delta^{\mathrm{ILSX}(m_1,m_2)}_{\theta_{\mathcal S}}(T)\le Cs\sqrt T\log T.$$
--
--   The result gives a uniform-in-parameter upper bound on the expected revenue lost to the price chosen by a seller who knows the demand parameter.
--
--   **Formalization Note** The estimate is any measurable least-squares minimizer selection, and $C$ may depend on the fixed model, noise process, and selection but not on $\theta_{\mathcal S}$ or $T$. The compressed feature vector is the restriction of $[1;Z_t]$ to $\mathcal S$. Regret is a nonnegative joint integral, equivalent to the paper's iterated expectation under the product construction. Since $\mathcal S$ is fixed in this statement, Remark 5's claim that $C$ is independent of $s$ is not formalized. The continuous-feature domain phrase is omitted; the shock process is fixed while $\theta_{\mathcal S}$ varies.
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), p. 5556, Theorem 2; p. 5557, Remark 5

import Mathlib
import Definitions.Def_BanKeskin_KnownSparsity_Model

open MeasureTheory
open scoped ENNReal

namespace BanKeskin.KnownSparsity

/-- Theorem 2, p. 5556: expected regret of known-support ILSX. -/
theorem theorem_2 {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Model d S Ω P) (N : NoiseConditions P M) (I : InteriorConditions M)
    (hest : M.IsEstimator) :
    ∃ C : ℝ, 0 < C ∧
      ∀ θ ∈ M.Theta, ∀ T : ℕ, 2 ≤ T →
        M.regret θ T ≤ ENNReal.ofReal
          (C * (S.card : ℝ) * Real.sqrt (T : ℝ) * Real.log (T : ℝ)) := by sorry

end BanKeskin.KnownSparsity
