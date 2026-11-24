-- Prove2me | Theorems.Thm_Formalism_REAL_CharId_sub_lsh_apply_single
-- name    : Formalism.REAL.CharId_sub_lsh_apply_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:46.424453+00:00
-- url     : https://prove2.me/theorems/1bf67d10-4d37-4e8c-b57e-e18d07ff0f5b
-- title:
--   REAL: Char Id sub lsh apply single
-- statement:
--   The REAL construction uses the Char Id sub lsh apply single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean#L126-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean#L126-L147

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.CharId_sub_lsh_apply_single {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) (hv : IsHW E ν v) (t : Fin n) :
    (CharId_M E - algebraMap ℂ (Module.End ℂ (Fin n → V)) (lsh ν t)) (Pi.single t v) =
      ∑ a ∈ univ.filter (fun a => t < a), twistedAction E a t (Pi.single a v) := by sorry
