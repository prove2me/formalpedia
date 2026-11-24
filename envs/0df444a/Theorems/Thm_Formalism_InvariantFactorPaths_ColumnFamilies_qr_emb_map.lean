-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_emb_map
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_emb_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:18.260708+00:00
-- url     : https://prove2.me/theorems/e52f923f-bce8-4e3e-8234-0b07b098e7c0
-- title:
--   Column Families: qr emb map
-- statement:
--   The Column Families construction uses the qr emb map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean#L65-L71

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_emb_map {k : ℕ} (h : S.card = k) (h' : (S.map Fin.castSuccEmb).card = k) :
    ⇑((S.map Fin.castSuccEmb).orderEmbOfFin h') = fun a => (S.orderEmbOfFin h a).castSucc := by sorry
