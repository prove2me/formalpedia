-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_coe_inv_of_det
-- name    : Formalism.DoubleCosetMeasures.P.Supp.coe_inv_of_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:18.644111+00:00
-- url     : https://prove2.me/theorems/74a70de6-37a5-44bf-af66-bf2c34907bc0
-- title:
--   Supp: coe inv of det
-- statement:
--   The Supp construction uses the coe inv of det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L245-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L245-L248

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp

theorem Formalism.DoubleCosetMeasures.P.Supp.coe_inv_of_det {K : Type} [CommRing K] {n : ℕ} (g : GL (Fin n) K)
    (hg : (g : Matrix (Fin n) (Fin n) K).det = 1) :
    ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K).adjugate := by sorry
