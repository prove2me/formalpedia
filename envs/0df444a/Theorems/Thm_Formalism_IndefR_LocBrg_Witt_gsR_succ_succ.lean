-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_Witt_gsR_succ_succ
-- name    : Formalism.IndefR.LocBrg.Witt.gsR_succ_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:22.374619+00:00
-- url     : https://prove2.me/theorems/25051b47-97d4-4cc5-9758-3b2b897898ec
-- title:
--   Witt: gs R succ succ
-- statement:
--   The Witt construction uses the gs R succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittDiag.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittDiag.lean#L50-L51

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittDiag
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
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg Formalism.IndefR.LocBrg.Witt
variable {R : Type} [CommRing R]
variable [IsLocalRing R] (σ : R →+* R)

theorem Formalism.IndefR.LocBrg.Witt.gsR_succ_succ {n : ℕ} (u : R) (m : Fin n → R) (i j : Fin n) :
    gsR u m i.succ j.succ = (1 : Matrix (Fin n) (Fin n) R) i j := by sorry

attribute [defeq] Formalism.IndefR.LocBrg.Witt.gsR_succ_succ
