-- Prove2me | Theorems.Thm_Formalism_L2_Pj_AvAlg_residue_aeval
-- name    : Formalism.L2.Pj.AvAlg.residue_aeval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:02.847867+00:00
-- url     : https://prove2.me/theorems/c1be0aa1-5012-4803-972a-706c90174a2c
-- title:
--   Av Alg: residue aeval
-- statement:
--   The Av Alg construction uses the residue aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AvMono.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AvMono.lean#L88-L92

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.AvAlg
variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem Formalism.L2.Pj.AvAlg.residue_aeval (α : B) (G : A[X]) :
    residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by sorry
