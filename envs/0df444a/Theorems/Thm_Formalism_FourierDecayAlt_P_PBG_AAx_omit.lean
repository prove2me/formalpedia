-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_AAx_omit
-- name    : Formalism.FourierDecayAlt.P.PBG.AAx_omit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:08.607802+00:00
-- url     : https://prove2.me/theorems/e0067157-8b42-4e06-936b-653fcc0ab5a7
-- title:
--   PBG: AAx omit
-- statement:
--   The PBG construction uses the AAx omit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHead.lean#L43-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHead.lean#L43-L70

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem Formalism.FourierDecayAlt.P.PBG.AAx_omit {A : Type} [Ring A] [Algebra ℂ A] (k r m : ℕ) (hm : m + 1 ≤ r)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (u : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < m → m + 1 ≤ p.val → xi a p = 0) :
    AAx k r E xi m (by omega) u = ∑ l0 : Fin (m + 1),
      (Matrix.of fun a l : Fin m => xi (Fin.castLE (by omega) a) (xR k r (m + 1) hm (l0.succAbove l))).det •
        qminor E (xR k r m (by omega)) (xR k r (m + 1) hm ∘ l0.succAbove) u := by sorry
