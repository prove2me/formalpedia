-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_isOpen_compl
-- name    : Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.isOpen_compl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:46.828346+00:00
-- url     : https://prove2.me/theorems/614fec16-e3f9-4f3f-a26d-bafdec1a3d0b
-- title:
--   Period Lattice Basis Lemmas: is Open compl
-- statement:
--   The Period Lattice Basis Lemmas construction uses the is Open compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L55-L56

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodLatticeBasisLemmas

theorem Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.isOpen_compl (L : PeriodPair) : IsOpen ((L.lattice : Set ℂ)ᶜ) := by sorry
