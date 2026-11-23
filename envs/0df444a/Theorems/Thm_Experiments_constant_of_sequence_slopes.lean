-- Prove2me | Theorems.Thm_Experiments_constant_of_sequence_slopes
-- name    : Experiments.constant_of_sequence_slopes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:06.755963+00:00
-- url     : https://prove2.me/theorems/f9364cd7-1cfd-42a9-8263-c0fad17b32f4
-- title:
--   Experiments: constant of sequence slopes
-- statement:
--   A continuous function whose difference quotients tend to `0` along one sequence of positive
--   steps `h n → 0`, at every point of `[0, t)`, is constant on `[0, t]`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/FiniteDifferenceSemigroup.lean#L25-L60
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/FiniteDifferenceSemigroup.lean#L25-L60

import Definitions.Def_Experiments_GeneratorBound
import Definitions.Def_Experiments_FiniteDifferenceSemigroup
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments

theorem Experiments.constant_of_sequence_slopes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {h : ℕ → ℝ} (hpos : ∀ n, 0 < h n)
    (hz : Tendsto h atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn f (Icc 0 t))
    (hquot : ∀ x ∈ Ico 0 t,
      Tendsto (fun n => (h n)⁻¹ • (f (x + h n) - f x)) atTop (𝓝 0)) :
    f t = f 0 := by sorry
