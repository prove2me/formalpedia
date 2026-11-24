-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_sepLemma
-- name    : Formalism.HermitianLattices.StabilizerLevels.PfB.sepLemma
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:10.038628+00:00
-- url     : https://prove2.me/theorems/30a397ee-044a-4624-9c86-1367b7a61c4c
-- title:
--   Pf B: sep Lemma
-- statement:
--   The Pf B construction uses the sep Lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L115-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L115-L196

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
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (w : HeightOneSpectrum (𝓞 F))
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers F w)

theorem Formalism.HermitianLattices.StabilizerLevels.PfB.sepLemma (g : ℕ) (hgw : (g : 𝓞 F) ∈ w.asIdeal) :
    ∃ (A : Subring (E ⊗[F] w.adicCompletion F)),
      Formalism.UG.tensInt (F := F) (w.adicCompletion F) (Formalism.UG.intOE E)
        (w.adicCompletionIntegers F).toSubring ≤ A ∧
      (⨅ m : ℕ, (Ideal.span {(g : A)}) ^ m) = ⊥ := by sorry
