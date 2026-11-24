-- Prove2me | Theorems.Thm_Formalism_L2_Pj_AvAlg_adjoin_eq_top_of_gen
-- name    : Formalism.L2.Pj.AvAlg.adjoin_eq_top_of_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:50.365095+00:00
-- url     : https://prove2.me/theorems/7fc03ddf-4c40-401b-ac51-a06888e32aae
-- title:
--   Av Alg: adjoin eq top of gen
-- statement:
--   The Av Alg construction uses the adjoin eq top of gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AvMono.lean#L56-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AvMono.lean#L56-L79

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

theorem Formalism.L2.Pj.AvAlg.adjoin_eq_top_of_gen [Module.Finite A B] (hinj : Function.Injective (algebraMap A B)) (α : B)
    (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X]) (hβ : Irreducible (aeval α f)) :
    Algebra.adjoin A {α} = ⊤ := by sorry
