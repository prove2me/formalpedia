-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_add_left
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.hB_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:59:09.302474+00:00
-- url     : https://prove2.me/theorems/18dbcd61-ec91-48fb-861e-d8ab9a29eb8b
-- title:
--   S4aux: h B add left
-- statement:
--   The S4aux construction uses the h B add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2686-L2687
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2686-L2687

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
variable (K : Type) {L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {K}
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

theorem Formalism.HermitianLatticeCounting.P.S4aux.hB_add_left (x d y : Fin n → L) : hB K Ph (x + d) y = hB K Ph x y + hB K Ph d y := by sorry
