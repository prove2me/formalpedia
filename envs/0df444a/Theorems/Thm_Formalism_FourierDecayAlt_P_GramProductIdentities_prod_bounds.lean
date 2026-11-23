-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_prod_bounds
-- name    : Formalism.FourierDecayAlt.P.GramProductIdentities.prod_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:51.45689+00:00
-- url     : https://prove2.me/theorems/e01ec141-53e4-479b-bf16-e5e3769398dc
-- title:
--   Gram Product Identities: prod bounds
-- statement:
--   The Gram Product Identities construction uses the prod bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L157-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L157-L184

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem Formalism.FourierDecayAlt.P.GramProductIdentities.prod_bounds {ι : Type} (g : ι → ℝ) (ε : ℝ) (hε : ε ≤ 1 / 2) :
    ∀ w : List ι, (∀ l ∈ w, |g l - 1| ≤ ε) →
      Real.exp (-2 * ε * w.length) ≤ (w.map g).prod ∧ (w.map g).prod ≤ Real.exp (ε * w.length) := by sorry
