-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_gmap_cj
-- name    : Formalism.MainNotions.J.gmap_cj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:08.664738+00:00
-- url     : https://prove2.me/theorems/6e216698-73c1-4bbb-8497-2b4cb37a115b
-- title:
--   J: gmap cj
-- statement:
--   The J construction uses the gmap cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean#L56-L59

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

theorem Formalism.MainNotions.J.gmap_cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    gmap (cj φ g) (latMap φ M) = latMap φ (gmap g M) := by sorry
