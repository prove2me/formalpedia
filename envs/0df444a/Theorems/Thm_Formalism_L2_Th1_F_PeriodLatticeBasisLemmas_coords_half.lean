-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_coords_half
-- name    : Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.coords_half
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:17.999797+00:00
-- url     : https://prove2.me/theorems/5eb4f682-4cfd-4ad6-ad4d-eb8f5c3c7ca6
-- title:
--   Period Lattice Basis Lemmas: coords half
-- statement:
--   The Period Lattice Basis Lemmas construction uses the coords half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L182-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L182-L191

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

theorem Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.coords_half (L : PeriodPair) {a b a' b' : ℤ}
    (h : (a' : ℂ) * L.ω₁ + b' * L.ω₂ = (a * L.ω₁ + b * L.ω₂) / 2) : a = 2 * a' ∧ b = 2 * b' := by sorry
