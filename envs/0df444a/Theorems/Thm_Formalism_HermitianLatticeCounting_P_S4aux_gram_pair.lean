-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_gram_pair
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.gram_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:59:11.973134+00:00
-- url     : https://prove2.me/theorems/e1618620-692d-4c57-afde-104451fbc6f9
-- title:
--   S4aux: gram pair
-- statement:
--   The S4aux construction uses the gram pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L788-L791
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L788-L791

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.gram_pair {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (m : ℕ) (f : Fin m → V) (c : Fin m → E) (j : Fin m) :
    h (∑ i, c i • f i) (f j) = ∑ i, c i * h (f i) (f j) := by sorry
