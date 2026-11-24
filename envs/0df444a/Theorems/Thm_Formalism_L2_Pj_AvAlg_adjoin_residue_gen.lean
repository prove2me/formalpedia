-- Prove2me | Theorems.Thm_Formalism_L2_Pj_AvAlg_adjoin_residue_gen
-- name    : Formalism.L2.Pj.AvAlg.adjoin_residue_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:30.259906+00:00
-- url     : https://prove2.me/theorems/2c5b4a19-f147-4bf1-a223-1c3035ac74a5
-- title:
--   Av Alg: adjoin residue gen
-- statement:
--   The Av Alg construction uses the adjoin residue gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AvMono.lean#L94-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AvMono.lean#L94-L107

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

theorem Formalism.L2.Pj.AvAlg.adjoin_residue_gen [Finite (ResidueField B)] :
    ∃ γ : ResidueField B, Algebra.adjoin (ResidueField A) {γ} = ⊤ := by sorry
