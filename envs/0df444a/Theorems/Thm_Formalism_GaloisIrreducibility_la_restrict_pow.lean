-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_la_restrict_pow
-- name    : Formalism.GaloisIrreducibility.la_restrict_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:03.6748+00:00
-- url     : https://prove2.me/theorems/8b960b50-df15-4e65-8c53-383400d26d5e
-- title:
--   Galois Irreducibility: la restrict pow
-- statement:
--   The Galois Irreducibility construction uses the la restrict pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/LemmaAOf.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/LemmaAOf.lean#L10-L16

import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_LemmaAOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Module Polynomial
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem Formalism.GaloisIrreducibility.la_restrict_pow (τ : Module.End K V) (W : Submodule K V) (hτ : ∀ v ∈ W, τ v ∈ W)
    (n : ℕ) (v : W) : (((τ.restrict hτ) ^ n) v : V) = (τ ^ n) v := by sorry
