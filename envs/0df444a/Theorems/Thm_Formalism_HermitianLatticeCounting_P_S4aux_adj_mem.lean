-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_adj_mem
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.adj_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:36.802894+00:00
-- url     : https://prove2.me/theorems/4ad1d4ab-c43c-49b7-a251-c98e602c9b59
-- title:
--   S4aux: adj mem
-- statement:
--   The S4aux construction uses the adj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L780-L786
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L780-L786

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.adj_mem {E : Type} [CommRing E] (O : Subring E) (m : ℕ) (G : Matrix (Fin m) (Fin m) E)
    (hG : ∀ i j, G i j ∈ O) : ∀ i j, G.adjugate i j ∈ O := by sorry
