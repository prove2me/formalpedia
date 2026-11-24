-- Prove2me | Theorems.Thm_Formalism_YangianSpanCharacter_P_key_alg
-- name    : Formalism.YangianSpanCharacter.P.key_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:22.260799+00:00
-- url     : https://prove2.me/theorems/223c0be4-42fd-43d4-856e-aac7fc708afc
-- title:
--   P: key alg
-- statement:
--   The P construction uses the key alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L107-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L107-L139

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem Formalism.YangianSpanCharacter.P.key_alg {a b ai bi mu lu mv lv hu hv η μ : A} {c : 𝕜}
    (ha2 : ai * a = 1) (hb2 : bi * b = 1) (hab : a * b = b * a)
    (h1 : lv * a = a * (lv + η)) (h2 : mu * b = b * (mu - μ)) (hη : c • η = lu - lv)
    (hμ : c • μ = mu - mv)
    (hR : c • (a * mu * (b * lv) - b * lv * (a * mu)) =
      a * (b * (mv * lv + hv)) - b * (a * (mu * lu + hu))) :
    (c - 1) • (mu * lv - lv * mu) = hv - hu - (mu * lu - lu * mu) := by sorry
