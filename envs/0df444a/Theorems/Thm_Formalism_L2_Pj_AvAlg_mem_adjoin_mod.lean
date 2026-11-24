-- Prove2me | Theorems.Thm_Formalism_L2_Pj_AvAlg_mem_adjoin_mod
-- name    : Formalism.L2.Pj.AvAlg.mem_adjoin_mod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:59.203938+00:00
-- url     : https://prove2.me/theorems/227a1eb5-cd1e-4f6e-b404-65be8db7b359
-- title:
--   Av Alg: mem adjoin mod
-- statement:
--   The Av Alg construction uses the mem adjoin mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AvMono.lean#L14-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AvMono.lean#L14-L47

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

theorem Formalism.L2.Pj.AvAlg.mem_adjoin_mod (α : B) (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X])
    (hβ : Irreducible (aeval α f)) :
    ∀ (n : ℕ) (b : B), ∃ s ∈ Algebra.adjoin A {α}, ∃ c : B, b = s + aeval α f ^ n * c := by sorry
