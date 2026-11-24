-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_shear_inv
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.shear_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:35.942628+00:00
-- url     : https://prove2.me/theorems/85351b19-54b8-4c21-b760-c131dad77383
-- title:
--   S4aux: shear inv
-- statement:
--   The S4aux construction uses the shear inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1417-L1422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1417-L1422

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
variable {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  (h : V →ₗ[E] V →ₗ⋆[E] E) {r : ℕ} (e : Fin r → V)

theorem Formalism.HermitianLatticeCounting.P.S4aux.shear_inv (t : Fin r → V) (ht : ∀ j i, h (t j) (e i) = 0) (v : V) :
    shear h e (fun j => - t j) (shear h e t v) = v := by sorry
