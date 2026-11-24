-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_eich_sub
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.Part2.eich_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:04.9908+00:00
-- url     : https://prove2.me/theorems/55e64742-4f1b-4e92-9684-de88435bd12d
-- title:
--   Part2: eich sub
-- statement:
--   The Part2 construction uses the eich sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1660-L1662
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1660-L1662

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
open Formalism.HermitianLatticeCounting.P.S4aux.Part2

theorem Formalism.HermitianLatticeCounting.P.S4aux.Part2.eich_sub {E V : Type} [CommRing E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E) (v w : V) :
    eich h x u s (v - w) = eich h x u s v - eich h x u s w := by sorry
