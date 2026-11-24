-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_off
-- name    : Formalism.FourierDecayAlt.P.NFx2.sb_off
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:18:48.897535+00:00
-- url     : https://prove2.me/theorems/aec2d8ec-0ad3-457a-952a-d6223fec0770
-- title:
--   NFx2: sb off
-- statement:
--   The NFx2 construction uses the sb off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L594-L654
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L594-L654

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}

theorem Formalism.FourierDecayAlt.P.NFx2.sb_off (h : SHyp P L0 QQ κ) (hP : P.OK) {σ ρ : M.Ty P} (hne : σ ≠ ρ) :
    (∀ v, lowerBlockAlt κ QQ σ ρ v = 0) ∨ ∃ m ∈ Icc 1 (P.k - 1), M.Up P m ρ σ ∧
      ∃ K : A, ∀ v, (v + ((M.rho P ρ m : ℝ) : ℂ) + 1) • lowerBlockAlt κ QQ σ ρ v = M.xC P σ v • K := by sorry
