-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_cj_symm_cj
-- name    : Formalism.MainNotions.J.cj_symm_cj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:57:09.004496+00:00
-- url     : https://prove2.me/theorems/625f307a-b84d-4c9c-9988-4a6833ee4d74
-- title:
--   J: cj symm cj
-- statement:
--   The J construction uses the cj symm cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean#L43-L44

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

theorem Formalism.MainNotions.J.cj_symm_cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : cj φ.symm (cj φ g) = g := by sorry
