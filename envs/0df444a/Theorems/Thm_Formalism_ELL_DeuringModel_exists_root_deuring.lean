-- Prove2me | Theorems.Thm_Formalism_ELL_DeuringModel_exists_root_deuring
-- name    : Formalism.ELL.DeuringModel.exists_root_deuring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:43.773499+00:00
-- url     : https://prove2.me/theorems/b043df8f-1b4c-4884-83bd-94bff3e5748d
-- title:
--   Deuring Model: exists root deuring
-- statement:
--   The Deuring Model construction uses the exists root deuring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Deuring.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Deuring.lean#L16-L25

import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Deuring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ELL
open Formalism.ELL.DeuringModel
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.DeuringModel.exists_root_deuring [IsAlgClosed K] (j : K) :
    ∃ a : K, a ^ 3 * (a ^ 3 - 24) ^ 3 = j * (a ^ 3 - 27) := by sorry
