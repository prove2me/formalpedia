-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_liesOver_span_of_natCast_mem_frobenius_orbits
-- name    : Formalism.FrobeniusOrbits.liesOver_span_of_natCast_mem_frobenius_orbits
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:39:23.882852+00:00
-- url     : https://prove2.me/theorems/80b1207d-53fc-4846-abbd-2a2fd568271a
-- title:
--   Frobenius Orbits: lies Over span of nat Cast mem frobenius orbits
-- statement:
--   The Frobenius Orbits construction uses the lies Over span of nat Cast mem frobenius orbits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L336-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L336-L342

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem Formalism.FrobeniusOrbits.liesOver_span_of_natCast_mem_frobenius_orbits {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [P.IsPrime]
    (p : ℕ) (hp : p.Prime) (hm : ((p : ℤ) : 𝓞 M) ∈ P) : P.LiesOver (span {(p : ℤ)}) := by sorry
