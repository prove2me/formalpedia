-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_gaAct_eq_dg
-- name    : Formalism.MainNotions.PlaneGram.gaAct_eq_dg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:27.398432+00:00
-- url     : https://prove2.me/theorems/0c81c5c3-d9a0-497b-a7a7-597ebf5b0b51
-- title:
--   Plane Gram: ga Act eq dg
-- statement:
--   The Plane Gram construction uses the ga Act eq dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L180-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L180-L182

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
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
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable {σ : Type}

theorem Formalism.MainNotions.PlaneGram.gaAct_eq_dg (D : TwistData K) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.gaAct G = dg D.ga G := by sorry
