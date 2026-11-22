-- Prove2me | solution 1 for tendsto_of_orderConvergesTo_of_isOrderContinuousNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:34.547723+00:00
-- url     : https://prove2.me/submissions/9083cfb5-a689-484d-ba62-742935dda778

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic

set_option autoImplicit true
@[expose] public section
public section
universe u
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution
    {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [NormedVectorLattice X] [IsOrderContinuousNorm X]
    {ι : Type u} [Preorder ι]
    {x : ι → X} {a : X} (hx : OrderConvergesTo x a) :
    Filter.Tendsto x Filter.atTop (nhds a) := by
  rcases hx with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  have hr_tend : Filter.Tendsto r Filter.atTop (nhds 0) :=
    IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero hranti hrnn hrglb
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hr_event := Metric.tendsto_nhds.mp hr_tend ε hε
  rcases hr_event.exists with ⟨k, hk⟩
  refine (hrevent k).mono fun i hi => ?_
  have hnorm_le : ‖x i - a‖ ≤ ‖r k‖ := by
    rw [← norm_abs_eq_norm (x i - a)]
    exact norm_le_norm_of_abs_le_abs (by
      rw [abs_abs, abs_of_nonneg (hrnn k)]
      exact hi)
  calc
    dist (x i) a = ‖x i - a‖ := dist_eq_norm _ _
    _ ≤ ‖r k‖ := hnorm_le
    _ = dist (r k) 0 := by rw [dist_eq_norm, sub_zero]
    _ < ε := hk
