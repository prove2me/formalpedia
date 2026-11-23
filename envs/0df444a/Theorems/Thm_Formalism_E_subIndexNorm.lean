-- Prove2me | Theorems.Thm_Formalism_E_subIndexNorm
-- name    : Formalism.E.subIndexNorm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:27.02995+00:00
-- url     : https://prove2.me/theorems/3c8c9ebf-d87e-493d-a37f-a0fa15375fe4
-- title:
--   E: sub Index Norm
-- statement:
--   The E construction uses the sub Index Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/SymGramPosSemidef.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/SymGramPosSemidef.lean#L19-L19

import Definitions.Def_Formalism_FockGram_FockGramProofs_FockHerm
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockSesq
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockPerm
import Definitions.Def_Formalism_FockGram_FockGramProofs_DetSymPow
import Definitions.Def_Formalism_FockGram_FockGramProofs_SubIndexNorm
import Mathlib
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_FockGram_FockGramProofs_HermDualOf
import Definitions.Def_Formalism_FockGram_FockGramProofs_HermitianTensorMulHermitian
import Definitions.Def_Formalism_FockGram_StatementSymPos
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Formalism_FockGram_SymGramPosSemidef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.E

theorem Formalism.E.subIndexNorm : SubIndexNorm := by sorry
