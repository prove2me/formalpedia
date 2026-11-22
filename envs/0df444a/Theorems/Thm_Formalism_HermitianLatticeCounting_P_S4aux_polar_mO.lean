-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_polar_mO
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.polar_mO
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:55.440829+00:00
-- url     : https://prove2.me/theorems/af6a4051-8b9d-46d5-845a-ae666414619a
-- title:
--   S4aux: polar m O
-- statement:
--   The S4aux construction uses the polar m O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3218-L3244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3218-L3244

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

theorem Formalism.HermitianLatticeCounting.P.S4aux.polar_mO (hU : Unram o O) {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
    (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O) (hH : IsHerm h) (C : Submodule O abelian₂)
    (hC : ∀ c ∈ C, ¬ IsUnit (h c c)) : ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ mO o O := by sorry
