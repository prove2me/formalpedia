-- Prove2me | Theorems.Thm_Formalism_L2_Host_CT_infDiag_coe
-- name    : Formalism.L2.Host.CT.infDiag_coe
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:40.181471+00:00
-- url     : https://prove2.me/theorems/dc402390-4db3-4ff5-9522-e73242238c64
-- title:
--   CT: inf Diag coe
-- statement:
--   The CT construction uses the inf Diag coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L442-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean#L442-L466

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host Formalism.L2.Host.CT
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]

theorem Formalism.L2.Host.CT.infDiag_coe (k : Eˣ) :
    ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) (k : E), 1) := by sorry
