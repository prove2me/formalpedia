-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_gauss_core
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.gauss_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:20.70999+00:00
-- url     : https://prove2.me/theorems/fa128665-7998-4b9e-a194-d019b0d44607
-- title:
--   S4aux: gauss core
-- statement:
--   The S4aux construction uses the gauss core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L592-L655
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L592-L655

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.gauss_core {U T : Type} [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (f : U → ℂ) (cond : AddChar T ℂ → ℕ) (q a ρ : ℕ)
    (hq : 2 ≤ q) (hρ : 4 ≤ ρ) (hT : Fintype.card T = q ^ a)
    (hc0 : ∀ ψ, cond ψ = 0 ↔ ψ = 0)
    (hcnt : ∀ i, 1 ≤ i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i)
    (hS : ∀ ψ : AddChar T ℂ, ψ ≠ 0 →
      ‖∑ u, ψ (Q u) * f u‖ ≤ ((q : ℝ) ^ (cond ψ * ρ))⁻¹ * (Fintype.card U : ℝ)) :
    ‖(∑ u ∈ univ.filter (fun u => Q u = 0), f u) - (∑ u, f u) / ((q : ℂ) ^ a)‖
      ≤ 2 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a) := by sorry
