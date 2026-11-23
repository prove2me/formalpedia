-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_exists_orth_family_gen
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.exists_orth_family_gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:53.077489+00:00
-- url     : https://prove2.me/theorems/a8e5ca6e-e5fe-4cdb-8c1b-c88b6ad824c0
-- title:
--   S4aux: exists orth family gen
-- statement:
--   The S4aux construction uses the exists orth family gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3410-L3431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3410-L3431

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
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

theorem Formalism.HermitianLatticeCounting.P.S4aux.exists_orth_family_gen [Nontrivial O] (J : Ideal O) (hJ : ∀ x ∈ J, ¬ IsUnit x)
    (hpol : ∀ C : Submodule O abelian₂, (∀ c ∈ C, ¬ IsUnit (h c c)) → ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ J)
    (hSD : SelfDual h) (ρ : ℕ) (hρ : ρ ≤ Module.finrank O abelian₂) :
    ∃ v : Fin ρ → abelian₂, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, IsUnit (h (v i) (v i)) := by sorry
