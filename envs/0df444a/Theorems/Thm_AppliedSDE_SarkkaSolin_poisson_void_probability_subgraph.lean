-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_poisson_void_probability_subgraph
-- name    : AppliedSDE.SarkkaSolin.poisson_void_probability_subgraph
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:44:52.748213+00:00
-- url     : https://prove2.me/theorems/eb448c4a-408f-4275-8349-455b4869786e
-- title:
--   Poisson point-process void probability beneath a deterministic graph
-- statement:
--   Särkkä and Solin (2019), Theorem 8.22 and equation (8.130), printed p. 159–160. Let T,M be nonnegative and φ a continuous function with 0≤φ(t)≤M for 0≤t≤T. Let N count points of a unit-intensity Poisson point process on the rectangle [0,T]×[0,M] lying on or beneath the graph of φ. Then P(N=0)=exp(-∫_0^T φ(t)dt). The process is represented as a Poisson point family with restricted planar Lebesgue intensity. Random envelopes require an additional conditional-independence theorem and are excluded here.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \mathbb P(N_{\mathrm{under}\ \phi}=0)=\exp\!\left(-\int_0^T\phi(t)\,\mathrm dt\right)
--   $$
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 8.22 and eq (8.130), printed pp. 159–160. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem AppliedSDE.SarkkaSolin.poisson_void_probability_subgraph
    {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → (ℝ × ℝ)}
    (T M : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ φ t)
    (hφM : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ M)
    (hPPP : IsPoissonPointFamily K X
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) M)) P) :
    let A : Set (ℝ × ℝ) :=
      {z | z.1 ∈ Set.Icc (0 : ℝ) T ∧ z.2 ∈ Set.Icc (0 : ℝ) (φ z.1)}
    P.real {ω | ProbabilityTheory.poissonRandomMeasure K X ω A = 0} =
      Real.exp (-(∫ t in (0 : ℝ)..T, φ t)) := by
  sorry
