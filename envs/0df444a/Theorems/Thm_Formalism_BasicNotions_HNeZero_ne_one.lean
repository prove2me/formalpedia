-- Prove2me | Theorems.Thm_Formalism_BasicNotions_HNeZero_ne_one
-- name    : Formalism.BasicNotions.HNeZero.ne_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:11:33.740547+00:00
-- url     : https://prove2.me/theorems/29a8cc91-1064-4557-8b39-8cdf301abc04
-- title:
--   HNe Zero: ne one
-- statement:
--   The HNe Zero construction uses the ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataHost.lean#L202-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataHost.lean#L202-L207

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
open Formalism Formalism.BasicNotions

theorem Formalism.BasicNotions.HNeZero.ne_one {R : Ranks} {H : Host R} {p : ℕ} (h : HNeZero H p) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) : (H.galE σ).2 ≠ 1 := by sorry
