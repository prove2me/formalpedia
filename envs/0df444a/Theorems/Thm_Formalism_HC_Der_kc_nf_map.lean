-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_nf_map
-- name    : Formalism.HC.Der.kc_nf_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:54.672446+00:00
-- url     : https://prove2.me/theorems/a886dbdc-83f7-4a82-914b-7fff33d0703f
-- title:
--   Der: kc nf map
-- statement:
--   The Der construction uses the kc nf map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcPair.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcPair.lean#L45-L53

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HC Formalism.HC.Der
open Ideal UniqueFactorizationMonoid

theorem Formalism.HC.Der.kc_nf_map {S : Type*} [CommRing S] [IsDedekindDomain S] (I : Ideal S) (hI : I ≠ ⊥)
    (f : Ideal S ≃* Ideal S) : normalizedFactors (f I) = (normalizedFactors I).map f := by sorry
