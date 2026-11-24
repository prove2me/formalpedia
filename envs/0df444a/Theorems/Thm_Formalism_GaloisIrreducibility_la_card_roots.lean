-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_la_card_roots
-- name    : Formalism.GaloisIrreducibility.la_card_roots
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:08.55881+00:00
-- url     : https://prove2.me/theorems/418cca03-a5fb-480c-a62a-9a7406f819f2
-- title:
--   Galois Irreducibility: la card roots
-- statement:
--   The Galois Irreducibility construction uses the la card roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/LemmaAOf.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/LemmaAOf.lean#L18-L21

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

theorem Formalism.GaloisIrreducibility.la_card_roots [IsAlgClosed K] [FiniteDimensional K V] (φ : Module.End K V) :
    (LinearMap.charpoly φ).roots.card = finrank K V := by sorry
