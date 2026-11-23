-- Prove2me | Theorems.Thm_FRI_folding_soundness
-- name    : FRI_folding_soundness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:11:27.107069+00:00
-- url     : https://prove2.me/theorems/3913c0eb-10b6-498a-81f0-07c8c621c2de
-- title:
--   FRI folding soundness: FRI folding soundness
-- statement:
--   FRI folding soundness theorem.
--
--   The probability of the bad event in a folding round i is bounded by the error function
--   err*(C_i, m_i, δ*). This establishes that folding preserves proximity with high probability.
--
--   The theorem is generic in the bound parameter B and works for any bound satisfying MCA:
--   - B = (1+ρ)/2 (proven bound from prior work, not formalized here)
--   - B = √ρ (conjectured Johnson bound)
--   - B = ρ (conjectured capacity bound)
--
--   **Reference:** Lemma 5.1 (page 13) - "Folding preserves agreement sets".
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L431-L479
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L431-L479

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_folding_soundness [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F)
    (bound : ℝ) (errorstar : ℕ → ℝ → ℝ)
    (h_mca : FRI_MCA_Hypothesis P bound errorstar)
    (f_0 : P.D_0 → F)
    (i : Fin P.num_foldings)
    (f_prev : FRI_domain P i → F)
    (h_deg : FRI_degree P i ≥ P.m i)
    (h_foldable : IsFoldable (FRI_domain P i) (P.m i))
    (h_delta_nonneg : 0 ≤ FRI_distance_star P f_0 bound)
    (h_delta_lt : FRI_distance_star P f_0 bound < 1 - bound)
    (h_error_nonneg : 0 ≤ FRI_error_fold P bound errorstar i (FRI_distance_star P f_0 bound)) :
    FRI_BadEvent_Prob P f_0 bound i f_prev ≤
      FRI_error_fold P bound errorstar i (FRI_distance_star P f_0 bound) := by sorry
