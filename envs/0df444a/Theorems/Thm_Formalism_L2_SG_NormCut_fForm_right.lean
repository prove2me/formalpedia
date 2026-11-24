-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_fForm_right
-- name    : Formalism.L2.SG.NormCut.fForm_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:45.3759+00:00
-- url     : https://prove2.me/theorems/b50f82e3-9068-4625-a6ef-a643b49ee2d7
-- title:
--   Norm Cut: f Form right
-- statement:
--   The Norm Cut construction uses the f Form right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L127-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L127-L139

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut
variable {I : Type*} [Group I] [Fintype I]

theorem Formalism.L2.SG.NormCut.fForm_right (U : Set I) (p : I → ℂ) (hr : ∀ x, ∀ u ∈ U, p (x * u) = p x * p u)
    (hn : ∀ u ∈ U, conj (p u) * p u = 1) (Gm : I → I → ℂ) (b : I)
    (hG : ∀ i j, Gm (i * b⁻¹) (j * b⁻¹) = Gm i j) (x y w : I) (hw : w ∈ U) :
    fForm p Gm x (b * y * w) = fForm p Gm x y := by sorry
