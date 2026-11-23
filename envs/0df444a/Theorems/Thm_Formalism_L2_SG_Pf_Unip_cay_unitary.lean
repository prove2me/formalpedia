-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_cay_unitary
-- name    : Formalism.L2.SG.Pf.Unip.cay_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:30.802154+00:00
-- url     : https://prove2.me/theorems/09530948-b8a8-4bb5-a008-588e788233e9
-- title:
--   Unip: cay unitary
-- statement:
--   The Unip construction uses the cay unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L260-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L260-L312

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]
variable {lv : ι → ℕ} {k : ℕ}
variable [StarRing K]

theorem Formalism.L2.SG.Pf.Unip.cay_unitary {J : Matrix ι ι K} {N : ℕ} {Z : Matrix ι ι K} (hZ : Zᴴ * J = -(J * Z))
    (hN : ((⅟2 : K) • Z) ^ N = 0) : (cay N Z)ᴴ * J * cay N Z = J := by sorry
