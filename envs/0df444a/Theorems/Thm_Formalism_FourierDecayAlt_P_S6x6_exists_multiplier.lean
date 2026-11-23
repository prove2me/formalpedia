-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_exists_multiplier
-- name    : Formalism.FourierDecayAlt.P.S6x6.exists_multiplier
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:45.337886+00:00
-- url     : https://prove2.me/theorems/29fc636e-db2a-4b61-a373-2adbd94b51c1
-- title:
--   S6x6: exists multiplier
-- statement:
--   The S6x6 construction uses the exists multiplier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L134-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L134-L170

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}

theorem Formalism.FourierDecayAlt.P.S6x6.exists_multiplier {L : Submodule ℤ E} (hL : IsFLattice E L)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsMaximal) (τ : E) :
    ∃ e : 𝓞 (maximalRealSubfield E),
      algebraMap (𝓞 (maximalRealSubfield E)) E e * τ - τ ∈ locAt E P L ∧
      ∀ Q : Ideal (𝓞 (maximalRealSubfield E)), Q.IsMaximal → Q ≠ P →
        algebraMap (𝓞 (maximalRealSubfield E)) E e * τ ∈ locAt E Q L := by sorry
