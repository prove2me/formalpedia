-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_ne_one_of_galE
-- name    : Formalism.FrobeniusOrbits.Misc2.ne_one_of_galE
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:46.07274+00:00
-- url     : https://prove2.me/theorems/04445a93-2222-41a7-abd4-bf560e3c45bd
-- title:
--   Misc2: ne one of gal E
-- statement:
--   The Misc2 construction uses the ne one of gal E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardExtendedGaloisGroup.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardExtendedGaloisGroup.lean#L26-L30

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Misc2

theorem Formalism.FrobeniusOrbits.Misc2.ne_one_of_galE {e q d : ℕ} (hqd : HypOdd q d) {L : Type} [Field L] [NumberField L]
    {ζ a b : L} (h : IsLayer (e + 2) q d ζ a b) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hσ : galE e ζ a b σ ≠ 1) : σ ≠ 1 := by sorry
