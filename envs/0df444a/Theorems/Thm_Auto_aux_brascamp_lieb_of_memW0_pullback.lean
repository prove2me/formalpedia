-- Prove2me | Theorems.Thm_Auto_aux_brascamp_lieb_of_memW0_pullback
-- name    : Auto.aux_brascamp_lieb_of_memW0_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:55:39.344892+00:00
-- url     : https://prove2.me/theorems/2059c438-2b72-42da-a65d-539a530fa910
-- title:
--   Auto: aux brascamp lieb of mem W0 pullback
-- statement:
--   The compositional Brascamp--Lieb step from the draft.  The two pullback hypotheses are
--   exactly the analytic content of the preceding fibre-integral proposition for the combined
--   injective map; keeping them explicit avoids concealing that geometric estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2835-L2878
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2835-L2878

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_brascamp_lieb_of_memW0_pullback
    {ι : Type*} [Fintype ι] {m l : ℕ} {d : ι → ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜]
    (f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜) (hf : ∀ i, MemW0 (f i))
    (pi : ∀ i, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (d i)))
    (hPullback : MemW0 (fun uv : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) ↦
      ∏ i, f i (pi i uv)))
    {C : ℝ} (hC : 0 ≤ C)
    (hPullback_bound :
      (∫ uv : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l),
        wienerEnvelope (fun uv ↦ ∏ i, f i (pi i uv)) 1 uv) ≤
        C * ∫ x : ∀ i, EuclideanSpace ℝ (Fin (d i)),
          wienerEnvelope (fun y ↦ ∏ i, f i (y i)) 1 x) :
    MemW0 (fun x : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (x i)) ∧
      (∀ u : EuclideanSpace ℝ (Fin m),
        MemW0 (fun v : EuclideanSpace ℝ (Fin l) ↦ ∏ i, f i (pi i (u, v)))) ∧
      MemW0 (fun u : EuclideanSpace ℝ (Fin m) ↦ ∫ v, ∏ i, f i (pi i (u, v))) ∧
      (∫ u : EuclideanSpace ℝ (Fin m),
        wienerEnvelope (fun u ↦ ∫ v, ∏ i, f i (pi i (u, v))) 1 u) ≤
        C * ∏ i, ∫ x, wienerEnvelope (f i) 1 x := by sorry
