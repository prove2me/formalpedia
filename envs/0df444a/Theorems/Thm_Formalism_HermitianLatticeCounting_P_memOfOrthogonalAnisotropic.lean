-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_memOfOrthogonalAnisotropic
-- name    : Formalism.HermitianLatticeCounting.P.memOfOrthogonalAnisotropic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:53.762606+00:00
-- url     : https://prove2.me/theorems/277d154d-182a-4959-bd4b-db1a00be36cf
-- title:
--   P: mem Of Orthogonal Anisotropic
-- statement:
--   The P construction uses the mem Of Orthogonal Anisotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L291-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L291-L293

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.memOfOrthogonalAnisotropic : Formalism.HermitianLatticeCounting.S6.MemOfOrthogonalAnisotropic := by sorry
