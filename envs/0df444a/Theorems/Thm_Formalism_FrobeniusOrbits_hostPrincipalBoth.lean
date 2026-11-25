-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_hostPrincipalBoth
-- name    : Formalism.FrobeniusOrbits.hostPrincipalBoth
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:16.34373+00:00
-- url     : https://prove2.me/theorems/f2b97f13-6b83-5bca-ac2c-7278d9129de4
-- title:
--   Frobenius Orbits: host Principal Both
-- statement:
--   The Frobenius Orbits construction uses the host Principal Both property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L377-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L377-L377

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

theorem Formalism.FrobeniusOrbits.hostPrincipalBoth : HostDiffSupport ∧ HostPrincipal := by sorry
