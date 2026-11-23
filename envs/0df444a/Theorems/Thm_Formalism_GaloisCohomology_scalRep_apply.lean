-- Prove2me | Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- name    : Formalism.GaloisCohomology.scalRep_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:00.608039+00:00
-- url     : https://prove2.me/theorems/6dfbf758-2557-4a51-ab7b-31fe766fa6f9
-- title:
--   Galois Cohomology: scal Rep apply
-- statement:
--   The Galois Cohomology construction uses the scal Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisCohomology/Statement.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisCohomology/Statement.lean#L39-L41

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_Formalism_GaloisCohomology_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open Formalism Formalism.GaloisCohomology

theorem Formalism.GaloisCohomology.scalRep_apply {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] (M : Type*)
    [AddCommGroup M] [Module R M] (ψ : Γ →* Rˣ) (g : Γ) (m : M) :
    scalRep M ψ g m = ((ψ g : Rˣ) : R) • m := by sorry

attribute [defeq] Formalism.GaloisCohomology.scalRep_apply
