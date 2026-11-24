-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_coreQ
-- name    : Formalism.HermitianLattices.StabilizerLevels.PfB.coreQ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:11:55.367885+00:00
-- url     : https://prove2.me/theorems/b44cd73e-30a7-4fba-8213-9dbee048141a
-- title:
--   Pf B: core Q
-- statement:
--   The Pf B construction uses the core Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L513-L559
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L513-L559

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.HermitianLattices.StabilizerLevels.PfB.coreQ (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (τ₁ τ₂ τ₃ : Gal(L/ℚ)) (h1 : galMap h.1 a b τ₁ = ((1, -1, 1) : GalL (e + 2)))
    (h2 : galMap h.1 a b τ₂ = ((1, 1, -1) : GalL (e + 2)))
    (h3 : galMap h.1 a b τ₃ = ((u5 (e + 2), 1, 1) : GalL (e + 2)))
    (X y : L) (hX : X ∈ hostE ζ a b) (hy : y ∈ hostE ζ a b) (m m' : ℤ) (hm : Squarefree m)
    (hm' : Squarefree m') (hXm : X ^ 2 = (m : L)) (hym : y ^ 2 = (m' : L))
    (r1 : τ₁ X * y = X * τ₁ y) (r2 : τ₂ X * y = X * τ₂ y) (r3 : τ₃ X * y = X * τ₃ y) : m = m' := by sorry
