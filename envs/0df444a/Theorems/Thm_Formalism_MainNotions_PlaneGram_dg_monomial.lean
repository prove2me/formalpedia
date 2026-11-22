-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial
-- name    : Formalism.MainNotions.PlaneGram.dg_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:56.444454+00:00
-- url     : https://prove2.me/theorems/9d7c2902-9895-4ece-b77c-b22e3086999f
-- title:
--   Plane Gram: dg monomial
-- statement:
--   The Plane Gram construction uses the dg monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MemPolKIff.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MemPolKIff.lean#L42-L47

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

theorem Formalism.MainNotions.PlaneGram.dg_monomial {σ : Type} (f : (σ →₀ ℕ) → K) (α : σ →₀ ℕ) (c : K) :
    dg f (monomial α c) = monomial α (f α * c) := by sorry
