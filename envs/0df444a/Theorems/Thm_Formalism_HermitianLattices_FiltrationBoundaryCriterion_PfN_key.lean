-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_key
-- name    : Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.key
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:46:54.967516+00:00
-- url     : https://prove2.me/theorems/aa7204f1-d658-4fc2-b35c-b21a53f9b225
-- title:
--   Pf N: key
-- statement:
--   The Pf N construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferentIdealConditions.lean#L332-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferentIdealConditions.lean#L332-L345

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
open NumberField IntermediateField Ideal
open scoped Pointwise
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.key (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ) (hr : r = 2 ∨ r = q)
    (𝔭 : Ideal (𝓞 (KinE ζ a b))) [𝔭.IsPrime] (hm𝔭 : ((r : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P) :
    cm (c • P) = 𝔭 ↔ ¬ cm P = 𝔭 := by sorry
