-- Prove2me | Theorems.Thm_EthierKurtz_martingale_problem_sde_representation
-- name    : EthierKurtz.martingale_problem_sde_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:53:13.438607+00:00
-- url     : https://prove2.me/theorems/dc68803b-fb00-4100-9351-c476d7e0c2c2
-- title:
--   Theorem 3.3 — martingale-problem solution represented by a Brownian SDE
-- statement:
--   A solution of the time-dependent diffusion martingale problem is represented on the completed product extension, without replacing the given process, by a weak Brownian stochastic integral equation solution.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3, Theorem 3.3, printed pp. 293–294 (PDF pp. 302–303); equations (3.3)–(3.5), printed p. 291 (PDF p. 300).

import Definitions.Def_EthierKurtz_SolvesSDEMartingaleProblem
import Definitions.Def_EthierKurtz_IsWeakSDESolution
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace EthierKurtz

/-- Representation on the source's specified completed product extension.
The original X is lifted by first projection, not replaced by a copy in law.
The filtration witness is constrained to be exactly the completed product past. -/
theorem martingale_problem_sde_representation
    {Ω Ω' : Type*} [m : MeasurableSpace Ω] [m' : MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (ℱ : Filtration ℝ≥0 m) (ℱ' : Filtration ℝ≥0 m')
    (σ : ℝ≥0 × SDEState d → SDEDiffusion d)
    (b : ℝ≥0 × SDEState d → SDEState d)
    (hσ : Measurable σ) (hb : Measurable b)
    (hlocal : ∀ K : Set (ℝ≥0 × SDEState d), IsCompact K →
      ∃ C : ℝ, ∀ z ∈ K, ‖σ z‖ ≤ C ∧ ‖b z‖ ≤ C)
    (μ : Measure (SDEState d)) [IsProbabilityMeasure μ]
    (X : ℝ≥0 → Ω → SDEState d)
    (hX : SolvesSDEMartingaleProblem P ℱ σ b μ X)
    (W' : ℝ≥0 → Ω' → SDEState d)
    (hW' : IsStandardBrownian P' W')
    (hW'adapt : ∀ t, Measurable[ℱ' t] (W' t))
    (hW'indep : ∀ t, Indep (ℱ' t)
      (MeasurableSpace.comap (fun w (r : Set.Ici t) => W' r.val w - W' t w)
        inferInstance) P') :
    ∃ ℋ : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (NullMeasurableSpace (Ω × Ω') (P.prod P'))),
      (∀ t, ℋ t =
        (MeasurableSpace.comap Prod.fst (ℱ t) ⊔
          MeasurableSpace.comap Prod.snd (ℱ' t)) ⊔
        MeasurableSpace.generateFrom {A : Set (Ω × Ω') |
          ∃ N : Set (Ω × Ω'), MeasurableSet N ∧ (P.prod P') N = 0 ∧ A ⊆ N}) ∧
      ∃ W : ℝ≥0 → NullMeasurableSpace (Ω × Ω') (P.prod P') → SDEState d,
        IsWeakSDESolution (P.prod P').completion ℋ σ b μ W
          (fun t w => X t w.1) := by sorry
