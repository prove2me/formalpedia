-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S4_assemblyNG2
-- name    : Formalism.HermitianLatticeCounting.Final.S4.assemblyNG2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:14.827852+00:00
-- url     : https://prove2.me/theorems/6c47f91c-6ceb-4947-ba91-5fd1287db6d3
-- title:
--   S4: assembly NG2
-- statement:
--   The S4 construction uses the assembly NG2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ValuationProductBound.lean#L63-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ValuationProductBound.lean#L63-L63

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_assemblyNG2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S4

theorem Formalism.HermitianLatticeCounting.Final.S4.assemblyNG2 : Formalism.HermitianLatticeCounting.S4.AssemblyNG2 := by sorry
