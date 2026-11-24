-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_gauss_inert
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.gauss_inert
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:22.352854+00:00
-- url     : https://prove2.me/theorems/3fd3c07d-ceff-4ae6-9584-0fcb4b1247aa
-- title:
--   S4aux: gauss inert
-- statement:
--   The S4aux construction uses the gauss inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2641-L2669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2641-L2669

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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

theorem Formalism.HermitianLatticeCounting.P.S4aux.gauss_inert (h2 : Module.finrank K L = 2) (n : ℕ) (Ph : Matrix (Fin n) (Fin n) L)
    (hPh : IsUnit Ph.det) (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) (φ : (Fin n → L) → ℂ)
    (hφ : ∀ u, ‖φ u‖ = 1)
    (hadd : ∀ u d, φ (u + d) = φ u * φ d *
      ψ (Algebra.trace K L (∑ i, ∑ j, u i * Ph i j * d j ^ Fintype.card K))) :
    ‖∑ u, φ u‖ ≤ (Fintype.card K : ℝ) ^ n := by sorry
