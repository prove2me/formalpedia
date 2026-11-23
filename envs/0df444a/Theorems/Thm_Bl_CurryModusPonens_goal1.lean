-- Prove2me | Theorems.Thm_Bl_CurryModusPonens_goal1
-- name    : Bl.CurryModusPonens.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:14.648802+00:00
-- url     : https://prove2.me/theorems/caed4dfa-e3e7-4eb1-b00a-876899f572a6
-- title:
--   Curry Modus Ponens: goal1
-- statement:
--   The Curry Modus Ponens construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/CurryModusPonens/CurryMp.lean#L27-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/CurryModusPonens/CurryMp.lean#L27-L54

import Mathlib
import Definitions.Def_Lemmata_CurryModusPonens_CurryMp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.CurryModusPonens

theorem Bl.CurryModusPonens.goal1 :
  ∀ (ι : Type u_1) (κ : Type u_2) [inst : Fintype.{u_1} ι] [inst_1 : Fintype.{u_2} κ],
  @MeasureTheory.MeasurePreserving.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} ι κ → Complex) (ι → κ → Complex)
    (@MeasureTheory.MeasureSpace.toMeasurableSpace.{max u_1 u_2} (Prod.{u_1, u_2} ι κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{max u_1 u_2, 0} (Prod.{u_1, u_2} ι κ)
        (@instFintypeProd.{u_1, u_2} ι κ inst inst_1) (fun (a : Prod.{u_1, u_2} ι κ) ↦ Complex)
        fun (i : Prod.{u_1, u_2} ι κ) ↦
        @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
          Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace))
    (@MeasureTheory.MeasureSpace.toMeasurableSpace.{max u_1 u_2} (ι → κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{u_1, u_2} ι inst (fun (a : ι) ↦ κ → Complex) fun (i : ι) ↦
        @MeasureTheory.MeasureSpace.pi.{u_2, 0} κ inst_1 (fun (a : κ) ↦ Complex) fun (i : κ) ↦
          @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
            Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace))
    (@Function.curry.{u_1, u_2, 1} ι κ Complex)
    (@MeasureTheory.MeasureSpace.volume.{max u_1 u_2} (Prod.{u_1, u_2} ι κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{max u_1 u_2, 0} (Prod.{u_1, u_2} ι κ)
        (@instFintypeProd.{u_1, u_2} ι κ inst inst_1) (fun (a : Prod.{u_1, u_2} ι κ) ↦ Complex)
        fun (i : Prod.{u_1, u_2} ι κ) ↦
        @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
          Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace))
    (@MeasureTheory.MeasureSpace.volume.{max u_1 u_2} (ι → κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{u_1, u_2} ι inst (fun (a : ι) ↦ κ → Complex) fun (i : ι) ↦
        @MeasureTheory.MeasureSpace.pi.{u_2, 0} κ inst_1 (fun (a : κ) ↦ Complex) fun (i : κ) ↦
          @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
            Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace)) := by sorry
