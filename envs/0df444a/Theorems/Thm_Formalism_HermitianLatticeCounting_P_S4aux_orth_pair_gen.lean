-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_gen
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.orth_pair_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:13.78567+00:00
-- url     : https://prove2.me/theorems/40b21fda-a21d-4a2d-bcb5-92fb1ed56cfd
-- title:
--   S4aux: orth pair gen
-- statement:
--   The S4aux construction uses the orth pair gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3260-L3264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3260-L3264

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
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

theorem Formalism.HermitianLatticeCounting.P.S4aux.orth_pair_gen {κ : Type} [Fintype κ] (v : κ → abelian₂) (x : abelian₂) (w : κ → O) :
    h x (∑ i, w i • v i) = ∑ i, star (w i) * h x (v i) := by sorry
