-- Prove2me | solution 1 for continuous_log_on_open_simply_connected_components
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T03:23:55.977966+00:00
-- url     : https://prove2.me/submissions/9c995ce8-fe4e-40da-955c-2d641a04f611

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Topology.Connected.LocallyConnected

open Set

/-- Choosing a continuous function for each open component gives a continuous
function when the choice depends only on the component itself. -/
theorem continuousOn_componentwise {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace X] (U : Set X) (hU : IsOpen U) (g : Set X → X → Y)
    (hg : ∀ x ∈ U, ContinuousOn (g (connectedComponentIn U x)) (connectedComponentIn U x)) :
    ContinuousOn (fun x => g (connectedComponentIn U x) x) U := by
  intro x hx
  let C := connectedComponentIn U x
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCo : IsOpen C := hU.connectedComponentIn
  have hfc : ContinuousOn (fun y => g (connectedComponentIn U y) y) C := by
    apply (hg x hx).congr
    intro y hy
    have heq : connectedComponentIn U x = connectedComponentIn U y := connectedComponentIn_eq hy
    change g (connectedComponentIn U y) y = g (connectedComponentIn U x) y
    rw [← heq]
  exact ((hfc x hxC).continuousAt (hCo.mem_nhds hxC)).continuousWithinAt

#print axioms continuousOn_componentwise

/-- A nonvanishing map admits a logarithm on an open set whose connected
components are all simply connected, even when the open set is disconnected. -/
theorem solution {X : Type} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (U : Set X) (hU : IsOpen U)
    (hsc : ∀ x ∈ U, IsSimplyConnected (connectedComponentIn U x))
    (F : X → ℂ) (hFc : ContinuousOn F U) (hFne : ∀ x ∈ U, F x ≠ 0) :
    ∃ f : X → ℂ, ContinuousOn f U ∧ EqOn (fun x => Complex.exp (f x)) F U := by
  classical
  have branch (C : Set X) (hC : IsOpen C ∧ IsSimplyConnected C ∧ C ⊆ U) :
      ∃ f : X → ℂ, ContinuousOn f C ∧ EqOn (fun x => Complex.exp (f x)) F C := by
    have hzero : 0 ∉ F '' C := by
      rintro ⟨x, hx, heq⟩
      exact hFne x (hC.2.2 hx) heq
    exact Complex.exists_continuousOn_eqOn_exp_comp hC.2.1 hC.1 (hFc.mono hC.2.2) hzero
  let g : Set X → X → ℂ := fun C =>
    if hC : IsOpen C ∧ IsSimplyConnected C ∧ C ⊆ U then Classical.choose (branch C hC)
    else fun _ => 0
  have hg (C : Set X) (hC : IsOpen C ∧ IsSimplyConnected C ∧ C ⊆ U) :
      ContinuousOn (g C) C ∧ EqOn (fun x => Complex.exp (g C x)) F C := by
    simpa only [g, dif_pos hC] using Classical.choose_spec (branch C hC)
  have hcomp (x : X) (hx : x ∈ U) :
      IsOpen (connectedComponentIn U x) ∧ IsSimplyConnected (connectedComponentIn U x) ∧
        connectedComponentIn U x ⊆ U :=
    ⟨hU.connectedComponentIn, hsc x hx, connectedComponentIn_subset U x⟩
  refine ⟨fun x => g (connectedComponentIn U x) x, ?_, ?_⟩
  · exact continuousOn_componentwise U hU g (fun x hx => (hg _ (hcomp x hx)).1)
  · intro x hx
    exact (hg _ (hcomp x hx)).2 (mem_connectedComponentIn hx)

#print axioms solution

