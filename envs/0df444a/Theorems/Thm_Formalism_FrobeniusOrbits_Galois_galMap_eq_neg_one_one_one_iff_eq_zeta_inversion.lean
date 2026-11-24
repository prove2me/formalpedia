-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_eq_neg_one_one_one_iff_eq_zeta_inversion
-- name    : Formalism.FrobeniusOrbits.Galois.galMap_eq_neg_one_one_one_iff_eq_zeta_inversion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:52:58.117363+00:00
-- url     : https://prove2.me/theorems/9612fb1a-7d60-4f6e-ad62-efc6f1d3aeb7
-- title:
--   Galois: gal Map eq neg one one one iff eq zeta inversion
-- statement:
--   The Galois construction uses the gal Map eq neg one one one iff eq zeta inversion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L130-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L130-L136

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Galois.galMap_eq_neg_one_one_one_iff_eq_zeta_inversion (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (τ : Gal(L/ℚ)) :
    galMap h.1 a b τ = ((-1, 1, 1) : GalL (e + 2)) ↔ τ = tau0 hqd h := by sorry
