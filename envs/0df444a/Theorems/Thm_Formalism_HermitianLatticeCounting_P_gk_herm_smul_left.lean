-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_smul_left
-- name    : Formalism.HermitianLatticeCounting.P.gk_herm_smul_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:37.314568+00:00
-- url     : https://prove2.me/theorems/e1aa22d5-c776-4ab9-b859-fd4425eba015
-- title:
--   P: gk herm smul left
-- statement:
--   The P construction uses the gk herm smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L699-L701
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L699-L701

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants Matrix

theorem Formalism.HermitianLatticeCounting.P.gk_herm_smul_left {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (u w : ι → ℂ) :
    herm H (c • u) w = c * herm H u w := by sorry
