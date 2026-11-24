-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_fForm_left
-- name    : Formalism.L2.SG.NormCut.fForm_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:44.614839+00:00
-- url     : https://prove2.me/theorems/cb01e7e6-2cac-462c-a739-b470d26e91ad
-- title:
--   Norm Cut: f Form left
-- statement:
--   The Norm Cut construction uses the f Form left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L108-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L108-L125

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

theorem Formalism.L2.SG.NormCut.fForm_left (U : Set I) (p : I → ℂ) (hl : ∀ x, ∀ u ∈ U, p (u * x) = p u * p x)
    (hn : ∀ u ∈ U, conj (p u) * p u = 1) (Gm : I → I → ℂ) (b : I)
    (hG : ∀ i j, Gm (b * i) (b * j) = Gm i j) (x y w : I) (hw : w ∈ U) :
    fForm p Gm (b * x * w) y = fForm p Gm x y := by sorry
