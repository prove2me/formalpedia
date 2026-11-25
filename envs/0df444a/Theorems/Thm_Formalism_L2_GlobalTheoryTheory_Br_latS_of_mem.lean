-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Br_latS_of_mem
-- name    : Formalism.L2.GlobalTheoryTheory.Br.latS_of_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:09.168007+00:00
-- url     : https://prove2.me/theorems/09323d11-9740-5fa1-a1c6-91f89d414bf5
-- title:
--   Br: lat S of mem
-- statement:
--   The Br construction uses the lat S of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/BlockActions/LatSOfMem.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/BlockActions/LatSOfMem.lean#L17-L21

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Br
open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct

theorem Formalism.L2.GlobalTheoryTheory.Br.latS_of_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) (hx : x ∈ Λ) :
    (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ := by sorry
