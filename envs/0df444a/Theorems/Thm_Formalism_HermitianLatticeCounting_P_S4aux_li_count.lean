-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_li_count
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.li_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:41.312207+00:00
-- url     : https://prove2.me/theorems/ffa8f0e4-232b-421a-bf75-83130fa1f76d
-- title:
--   S4aux: li count
-- statement:
--   The S4aux construction uses the li count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2422-L2445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2422-L2445

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
variable {F : Type} [Field F] [Fintype F]

theorem Formalism.HermitianLatticeCounting.P.S4aux.li_count [DecidableEq F] {m n : ℕ} (Fs : Fin m → Finset (Fin n → F)) (c : ℕ)
    (hc : ∀ j, (Fs j).card = c) (hc0 : 0 < c)
    [DecidablePred fun Y : Fin m → Fin n → F => LinearIndependent F Y] :
    (((Fintype.piFinset Fs).filter fun Y => LinearIndependent F Y).card : ℝ) ≤ (c : ℝ) ^ m ∧
    (c : ℝ) ^ m - (Fintype.card F : ℝ) ^ m * (c : ℝ) ^ m / c
      ≤ (((Fintype.piFinset Fs).filter fun Y => LinearIndependent F Y).card : ℝ) := by sorry
