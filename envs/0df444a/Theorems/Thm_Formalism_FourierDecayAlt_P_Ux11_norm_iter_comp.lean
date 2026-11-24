-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_norm_iter_comp
-- name    : Formalism.FourierDecayAlt.P.Ux11.norm_iter_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:13.045176+00:00
-- url     : https://prove2.me/theorems/93cb959a-2225-4f7f-b48b-b66a17b17610
-- title:
--   Ux11: norm iter comp
-- statement:
--   The Ux11 construction uses the norm iter comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L124-L129

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.Ux11.norm_iter_comp {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : F →L[ℝ] G) {g : X → F} {Ω : Set X} {n : WithTop ℕ∞} (hg : ContDiffOn ℝ n g Ω)
    (hΩ : IsOpen Ω) {x : X} (hx : x ∈ Ω) {q : ℕ} (hq : (q : WithTop ℕ∞) ≤ n) :
    ‖iteratedFDeriv ℝ q (fun y => L (g y)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ q g x‖ := by sorry
