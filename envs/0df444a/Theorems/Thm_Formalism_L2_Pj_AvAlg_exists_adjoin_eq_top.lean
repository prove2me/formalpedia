-- Prove2me | Theorems.Thm_Formalism_L2_Pj_AvAlg_exists_adjoin_eq_top
-- name    : Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:43.786876+00:00
-- url     : https://prove2.me/theorems/5732d271-3a3b-4781-94c6-bba14f7bf2c7
-- title:
--   Av Alg: exists adjoin eq top
-- statement:
--   The Av Alg construction uses the exists adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AvMono.lean#L109-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AvMono.lean#L109-L165

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

theorem Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top [Module.Finite A B] [Finite (ResidueField A)]
    (hinj : Function.Injective (algebraMap A B)) : ∃ α : B, Algebra.adjoin A {α} = ⊤ := by sorry
