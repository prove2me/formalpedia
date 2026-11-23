-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_right
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.orth_pair_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:24.170965+00:00
-- url     : https://prove2.me/theorems/f4da4862-9c5f-49db-a041-69f49bae9837
-- title:
--   S4aux: orth pair right
-- statement:
--   The S4aux construction uses the orth pair right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3252-L3258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3252-L3258

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.orth_pair_right {κ : Type} [Fintype κ] (v : κ → abelian₂) (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (j : κ) (w : κ → O) : h (v j) (∑ i, w i • v i) = star (w j) * h (v j) (v j) := by sorry
