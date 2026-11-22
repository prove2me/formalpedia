-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_cj_mem_isom
-- name    : Formalism.MainNotions.J.cj_mem_isom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:00.480143+00:00
-- url     : https://prove2.me/theorems/ba4388ae-0382-415b-b392-d1cbd4abf035
-- title:
--   J: cj mem isom
-- statement:
--   The J construction uses the cj mem isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean#L85-L88

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
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.MainNotions.J.cj_mem_isom {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {g : V ≃ₗ[K] V}
    (hg : g ∈ isom h) : cj φ g ∈ isom h' := by sorry
