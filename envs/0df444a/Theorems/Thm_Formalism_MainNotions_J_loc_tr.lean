-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_loc_tr
-- name    : Formalism.MainNotions.J.loc_tr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:59.250421+00:00
-- url     : https://prove2.me/theorems/440c861e-c2a9-4885-9686-9d0445023c17
-- title:
--   J: loc tr
-- statement:
--   The J construction uses the loc tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean#L61-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean#L61-L77

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

theorem Formalism.MainNotions.J.loc_tr (φ : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) (M : Submodule (𝓞 K) V) :
    loc (K := K) p (latMap φ M) = latMap φ (loc (K := K) p M) := by sorry
