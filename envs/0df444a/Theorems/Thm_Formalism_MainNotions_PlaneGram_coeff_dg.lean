-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_dg
-- name    : Formalism.MainNotions.PlaneGram.coeff_dg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:53.529959+00:00
-- url     : https://prove2.me/theorems/eef74dbc-8c71-44d3-b7a8-bd0866a082a3
-- title:
--   Plane Gram: coeff dg
-- statement:
--   The Plane Gram construction uses the coeff dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MemPolKIff.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MemPolKIff.lean#L49-L58

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_LiftBoundOfHypotheses
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
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

theorem Formalism.MainNotions.PlaneGram.coeff_dg {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) (α : σ →₀ ℕ) :
    (dg f F).coeff α = f α * F.coeff α := by sorry
