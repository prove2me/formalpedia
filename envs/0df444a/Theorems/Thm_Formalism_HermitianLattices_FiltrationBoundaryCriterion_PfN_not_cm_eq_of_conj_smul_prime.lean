-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_not_cm_eq_of_conj_smul_prime
-- name    : Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.not_cm_eq_of_conj_smul_prime
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:17.152814+00:00
-- url     : https://prove2.me/theorems/299290d0-033a-48dc-bd4e-fad74bc4a27a
-- title:
--   Pf N: not cm eq of conj smul prime
-- statement:
--   The Pf N construction uses the not cm eq of conj smul prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferentIdealConditions.lean#L280-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferentIdealConditions.lean#L280-L302

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
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

theorem Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.not_cm_eq_of_conj_smul_prime (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ)
    (hr : r = 2 ∨ r = q) (𝔭 : Ideal (𝓞 (KinE ζ a b)))
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P)
    (h1 : cm P = 𝔭) (h2 : cm (c • P) = 𝔭) : False := by sorry
