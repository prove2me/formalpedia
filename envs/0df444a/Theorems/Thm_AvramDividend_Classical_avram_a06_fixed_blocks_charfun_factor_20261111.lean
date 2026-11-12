-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_blocks_charfun_factor_20261111
-- name    : AvramDividend.Classical.avram_a06_fixed_blocks_charfun_factor_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:47:51.321198+00:00
-- url     : https://prove2.me/theorems/0190fb85-0b7e-4c84-99f9-468a71e2fafa
-- title:
--   Characteristic functions of disjoint deterministic mark-block sums factorise
-- statement:
--   The Fourier transform of the vector of successive disjoint deterministic mark-block sums factorises into the product of individual characteristic functions. This is an immediate consequence of the already Proved deterministic mark-block independence theorem e5df9e82 and the Mathlib characteristic-function characterisation of finite independence. It is the fixed-count ingredient for the open random-count mixing theorem 23364f73 on the A06 selected route.

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_fixed_blocks_charfun_factor_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (m : Fin (n + 1) → ℕ) (hm : Monotone m)
    (Y : ℕ → Ω → ℝ)
    (hY : ∀ k, Measurable (Y k)) (hIndep : iIndepFun Y P) :
    ∀ t : WithLp 2 (Fin n → ℝ),
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
          ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
        ∏ i : Fin n, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
          (t.ofLp i) := by sorry
