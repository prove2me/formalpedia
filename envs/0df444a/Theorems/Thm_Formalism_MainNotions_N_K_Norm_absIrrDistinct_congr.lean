-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_K_Norm_absIrrDistinct_congr
-- name    : Formalism.MainNotions.N.K.Norm.absIrrDistinct_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:52.77382+00:00
-- url     : https://prove2.me/theorems/ac6fe960-066c-4dbc-8f2a-015e0c4dec9f
-- title:
--   Norm: abs Irr Distinct congr
-- statement:
--   The Norm construction uses the abs Irr Distinct congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L272-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L272-L317

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {Kf : Type} [Field Kf] {Γ : Type} [Group Γ] {V V' : Type} [AddCommGroup V] [Module Kf V]
  [AddCommGroup V'] [Module Kf V'] {ρ : Representation Kf Γ V} {ρ' : Representation Kf Γ V'}
  (e : V ≃ₗ[Kf] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem Formalism.MainNotions.N.K.Norm.absIrrDistinct_congr (h : AbsIrrDistinct ρ) : AbsIrrDistinct ρ' := by sorry
