-- Prove2me | solution 1 for unitaryDense_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:04:20.369148+00:00
-- url     : https://prove2.me/submissions/fe039ee6-d3a9-4689-a056-5a00526f162f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Derived

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI.UnitaryDenseWork
theorem _root_.solution (h : PI.FramesDense) : PI.UnitaryDense := by
  intro n P hP
  let e : Unit × Fin n × Fin n ≃ Fin n × Fin n := Equiv.punitProd _
  have hR : rename e.symm P = 0 := by
    refine h Unit n (fun _ => 1) (fun _ => Matrix.PosDef.one) (rename e.symm P) ?_
    intro y hy
    rw [eval_rename]
    have h1 := hP (y ()) (by simpa using hy ())
    exact h1
  exact rename_injective _ e.symm.injective (by rw [hR, map_zero])
