-- Prove2me | Theorems.Thm_Formalism_YangianSpanCharacter_P_key_mod
-- name    : Formalism.YangianSpanCharacter.P.key_mod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:39.733253+00:00
-- url     : https://prove2.me/theorems/699ba699-6a41-4580-9537-5500bf564284
-- title:
--   P: key mod
-- statement:
--   The P construction uses the key mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L213-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L213-L237

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
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}

theorem Formalism.YangianSpanCharacter.P.key_mod (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hu1 : u + 1 ∈ S) (hv : v ∈ S)
    (hv1 : v + 1 ∈ S) (huv : u ≠ v) :
    (u - v - 1) • (mf t τinv u * lf t τinv v - lf t τinv v * mf t τinv u) =
      hf τinv q v - hf τinv q u - (mf t τinv u * lf t τinv u - lf t τinv u * mf t τinv u) := by sorry
