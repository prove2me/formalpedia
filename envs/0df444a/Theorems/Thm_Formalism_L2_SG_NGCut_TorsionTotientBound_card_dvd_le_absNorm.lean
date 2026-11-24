-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_card_dvd_le_absNorm
-- name    : Formalism.L2.SG.NGCut.TorsionTotientBound.card_dvd_le_absNorm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:19.939891+00:00
-- url     : https://prove2.me/theorems/274ab96d-12dc-4802-8a42-62ddeb717f3c
-- title:
--   Torsion Totient Bound: card dvd le abs Norm
-- statement:
--   The Torsion Totient Bound construction uses the card dvd le abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/TwoLeAbsNormPrime.lean#L17-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/TwoLeAbsNormPrime.lean#L17-L47

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TwoLeAbsNormPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound
variable {E : Type} [Field E] [NumberField E]

theorem Formalism.L2.SG.NGCut.TorsionTotientBound.card_dvd_le_absNorm (M : Ideal (𝓞 E)) (hM : M ≠ ⊥) (D : Finset (Ideal (𝓞 E)))
    (hD : ∀ I ∈ D, I ∣ M) : D.card ≤ Ideal.absNorm M := by sorry
