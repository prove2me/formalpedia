-- Prove2me | Theorems.Thm_BERicci_Stab_lemma_5_9
-- name    : BERicci.Stab.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:36.831604+00:00
-- url     : https://prove2.me/theorems/ab71d2a5-4d69-42de-a3b6-a242cbaab647
-- title:
--   Lemma 5.9 — convergence of heat flows and generators along RCD(K,∞) measures
-- statement:
--   Let $m_n\to m_\infty$ in $\mathcal P_2(X)$, with every $(X,d,m_n)$ and the limit an $\mathrm{RCD}(K,\infty)$ space. Let $\mathcal E_n=2\operatorname{Ch}_{m_n}$, and let $P_t^n$ be its heat semigroup with generator $\Delta_n$. Suppose $f_n\to f_\infty$ in the sense of Definition 5.6 and the functions are uniformly bounded in $L^\infty$. Then
--
--   $$P_t^n f_n\longrightarrow P_t^\infty f_\infty\quad(t\ge0),\qquad
--     \Delta_nP_t^n f_n\longrightarrow\Delta_\infty P_t^\infty f_\infty\quad(t>0),$$
--
--   each according to Definition 5.6. The result supplies the heat-flow limits used when passing the distributional Bakry–Émery inequality to the limit.
--
--   **Formalization Note** The stated common-space $\mathrm{RCD}$ hypothesis includes full support on $X$, narrowing the ambient reduction on p. 63. Generator outputs are named by witnesses to their defining relation. Measurability of the selected function representatives is explicit, so graph-law pushforwards cannot collapse to zero.
-- source:
--   arXiv:1209.5786v4, Lemma 5.9, p. 66

import Mathlib
import Definitions.Def_BERicci_Stab_Convergence

namespace BERicci.Stab

open MeasureTheory Filter Topology

/-- Lemma 5.9, p. 66: stability of heat flow and its generator. -/
theorem lemma_5_9 {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : ℕ → Measure X) (mlim : Measure X) (K : ℝ)
    (P : ∀ n, ℝ → (X → ℝ) → X → ℝ)
    (Plim : ℝ → (X → ℝ) → X → ℝ)
    (f : ℕ → X → ℝ) (flim : X → ℝ)
    (lap : ∀ n, ℝ → X → ℝ) (laplim : ℝ → X → ℝ)
    (hm : ∀ n, BERicci.Gamma.IsRCDInfty (m n) K)
    (hmlim : BERicci.Gamma.IsRCDInfty mlim K)
    (hmconv : Tendsto (fun n => BERicci.Gamma.W2sq (m n) mlim) atTop (𝓝 0))
    (hP : ∀ n, BERicci.Gamma.IsHeatSemigroup (m n) (limitEnergy (m n)) (P n))
    (hPlim : BERicci.Gamma.IsHeatSemigroup mlim (limitEnergy mlim) Plim)
    (hgen : ∀ n t, 0 < t → BERicci.Gamma.IsGenerator (m n) (limitEnergy (m n))
      (P n t (f n)) (lap n t))
    (hgenlim : ∀ t, 0 < t → BERicci.Gamma.IsGenerator mlim (limitEnergy mlim)
      (Plim t flim) (laplim t))
    (hmeasP : ∀ n t, 0 ≤ t → Measurable (P n t (f n)))
    (hmeasPlim : ∀ t, 0 ≤ t → Measurable (Plim t flim))
    (hmeasLap : ∀ n t, 0 < t → Measurable (lap n t))
    (hmeasLaplim : ∀ t, 0 < t → Measurable (laplim t))
    (hf : ScalarConverges m mlim f flim)
    (hbounded : ∃ C : ℝ, 0 ≤ C ∧
      (∀ n, ∀ᵐ x ∂m n, |f n x| ≤ C) ∧ ∀ᵐ x ∂mlim, |flim x| ≤ C) :
    (∀ t, 0 ≤ t → ScalarConverges m mlim
      (fun n => P n t (f n)) (Plim t flim)) ∧
    (∀ t, 0 < t → ScalarConverges m mlim
      (fun n => lap n t) (laplim t)) := by sorry

end BERicci.Stab
