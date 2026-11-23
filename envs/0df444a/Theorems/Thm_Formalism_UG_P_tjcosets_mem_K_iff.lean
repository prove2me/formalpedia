-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_mem_K_iff
-- name    : Formalism.UG.P.tjcosets_mem_K_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:41.617448+00:00
-- url     : https://prove2.me/theorems/2eb5cb3e-e34e-48c2-b97a-570bf81338fd
-- title:
--   P: tjcosets mem K iff
-- statement:
--   The P construction uses the tjcosets mem K iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L119-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L119-L146

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L]
variable (O : Subring L) [IsLocalRing O]
variable {O}

theorem Formalism.UG.P.tjcosets_mem_K_iff (n : ℕ) (U : GL (Fin n) L) :
    U ∈ GLint (Fin n) O ↔ (∀ a b, (U : Matrix (Fin n) (Fin n) L) a b ∈ O) ∧
      (∀ a b, ((U⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b ∈ O) := by sorry
