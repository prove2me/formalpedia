-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_K_eval
-- name    : Formalism.FourierDecayAlt.P.NFx2.sb_K_eval
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:16:57.828443+00:00
-- url     : https://prove2.me/theorems/634eebe3-ffe9-47c2-8b6f-d177173348ab
-- title:
--   NFx2: sb K eval
-- statement:
--   The NFx2 construction uses the sb K eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L705-L726
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L705-L726

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

theorem Formalism.FourierDecayAlt.P.NFx2.sb_K_eval (h : SHyp P L0 QQ κ) (hP : P.OK) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ σ : M.Ty P}
    (hup : M.Up P l ρ σ) {Y : ℂ} (hY : Reg P Y) :
    (Y + ((M.rho P ρ l : ℝ) : ℂ) + 1)⁻¹ • sb_K κ QQ l ρ σ = (M.xC P σ Y)⁻¹ • lowerBlockAlt κ QQ σ ρ Y := by sorry
