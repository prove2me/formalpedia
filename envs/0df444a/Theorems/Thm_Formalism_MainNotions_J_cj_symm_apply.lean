-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_cj_symm_apply
-- name    : Formalism.MainNotions.J.cj_symm_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:57:18.766531+00:00
-- url     : https://prove2.me/theorems/daa55e1e-8a2b-4cda-afb6-b936954ada3a
-- title:
--   J: cj symm apply
-- statement:
--   The J construction uses the cj symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean#L40-L41

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem Formalism.MainNotions.J.cj_symm_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') :
    (cj φ g).symm y = φ (g.symm (φ.symm y)) := by sorry
