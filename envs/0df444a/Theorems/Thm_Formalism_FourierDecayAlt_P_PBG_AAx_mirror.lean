-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_AAx_mirror
-- name    : Formalism.FourierDecayAlt.P.PBG.AAx_mirror
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:10:44.786975+00:00
-- url     : https://prove2.me/theorems/091e9e4a-b302-5db8-8db3-2e90b39004c6
-- title:
--   PBG: AAx mirror
-- statement:
--   The PBG construction uses the AAx mirror property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L274-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L274-L327

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
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
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}
open scoped Classical

theorem Formalism.FourierDecayAlt.P.PBG.AAx_mirror (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : Formalism.REAL.GlRel E)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (ℓ : ℂ)
    (hsupp : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < m → y a p ≠ 0 → r + k < p.val) :
    C3.AAx k r (Emir E) (fun a q => ep q * y a (rv q)) m hm (-ℓ) =
      ((∏ l : Fin m, ep (xR k r m hm l)) * (-1) ^ m) • C3.AAv k r E y m hm ℓ := by sorry
