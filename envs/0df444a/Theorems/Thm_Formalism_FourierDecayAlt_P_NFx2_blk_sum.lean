-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_sum
-- name    : Formalism.FourierDecayAlt.P.NFx2.blk_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:19:05.542178+00:00
-- url     : https://prove2.me/theorems/41877553-fd16-4a18-8000-223c202683e6
-- title:
--   NFx2: blk sum
-- statement:
--   The NFx2 construction uses the blk sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L333-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L333-L335

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)

theorem Formalism.FourierDecayAlt.P.NFx2.blk_sum {R : M.Ty P → M.Ty P → Prop} {ι : Type} (s : Finset ι) {X : ι → A} (hX : ∀ i ∈ s, GlobalTheory κ R (X i)) :
    GlobalTheory κ R (∑ i ∈ s, X i) := by sorry
