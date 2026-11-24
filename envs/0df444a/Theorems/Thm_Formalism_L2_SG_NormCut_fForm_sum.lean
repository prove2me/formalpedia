-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_fForm_sum
-- name    : Formalism.L2.SG.NormCut.fForm_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:34.091873+00:00
-- url     : https://prove2.me/theorems/856c3f6b-e7df-4a5e-94c9-f2fa25e33971
-- title:
--   Norm Cut: f Form sum
-- statement:
--   The Norm Cut construction uses the f Form sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L141-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L141-L166

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

theorem Formalism.L2.SG.NormCut.fForm_sum (U : Set I) (p : I → ℂ) (h0 : ∀ x, x ∉ U → p x = 0)
    (hr : ∀ x, ∀ w ∈ U, p (x * w) = p x * p w) (hn : ∀ w ∈ U, conj (p w) * p w = 1)
    (hU : (Nat.card U : ℂ) ≠ 0) (Gm : I → I → ℂ) :
    ∑ x : I, ∑ y : I, fForm p Gm x y =
      (Nat.card U : ℂ) ^ 2 * ∑ i, ∑ j, conj (gamOf U p (i * j⁻¹)) * Gm i j := by sorry
