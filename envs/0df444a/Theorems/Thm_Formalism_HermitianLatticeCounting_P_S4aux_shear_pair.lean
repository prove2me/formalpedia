-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_shear_pair
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.shear_pair
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:35.528818+00:00
-- url     : https://prove2.me/theorems/3aeb6e76-5ca6-456b-87b9-33b8e361fadb
-- title:
--   S4aux: shear pair
-- statement:
--   The S4aux construction uses the shear pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1413-L1415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1413-L1415

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.shear_pair (t : Fin r → V) (ht : ∀ j i, h (t j) (e i) = 0) (v : V) (i : Fin r) :
    h (shear h e t v) (e i) = h v (e i) := by sorry
