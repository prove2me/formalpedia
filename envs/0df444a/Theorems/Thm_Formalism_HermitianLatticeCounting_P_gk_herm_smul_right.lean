-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_smul_right
-- name    : Formalism.HermitianLatticeCounting.P.gk_herm_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:03:19.236239+00:00
-- url     : https://prove2.me/theorems/f26c2ea9-47ef-4968-bc75-0019a21f0dab
-- title:
--   P: gk herm smul right
-- statement:
--   The P construction uses the gk herm smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L703-L705
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L703-L705

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

theorem Formalism.HermitianLatticeCounting.P.gk_herm_smul_right {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (u w : ι → ℂ) :
    herm H u (c • w) = star c * herm H u w := by sorry
