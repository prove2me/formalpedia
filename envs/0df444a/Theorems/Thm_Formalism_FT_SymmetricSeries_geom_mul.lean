-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_geom_mul
-- name    : Formalism.FT.SymmetricSeries.geom_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:27.137311+00:00
-- url     : https://prove2.me/theorems/c84c82c1-6e01-48ce-ad3c-31781831942a
-- title:
--   Symmetric Series: geom mul
-- statement:
--   The Symmetric Series construction uses the geom mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L50-L56

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
open PowerSeries

theorem Formalism.FT.SymmetricSeries.geom_mul (a : R) : (1 - C a * X) * PowerSeries.mk (fun m => a ^ m) = 1 := by sorry
