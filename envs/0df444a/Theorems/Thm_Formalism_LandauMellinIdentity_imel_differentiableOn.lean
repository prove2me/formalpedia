-- Prove2me | Theorems.Thm_Formalism_LandauMellinIdentity_imel_differentiableOn
-- name    : Formalism.LandauMellinIdentity.imel_differentiableOn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:51:39.819946+00:00
-- url     : https://prove2.me/theorems/8c8844bc-6072-469e-bc20-f42383a8fb73
-- title:
--   Landau Mellin Identity: imel differentiable On
-- statement:
--   The Landau Mellin Identity construction uses the imel differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauEq.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauEq.lean#L15-L29

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open Formalism.LandauMellinIdentity

theorem Formalism.LandauMellinIdentity.imel_differentiableOn {H : ℝ → ℝ} {a : ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    (hint : ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) :
    DifferentiableOn ℂ (Imel H) {s : ℂ | a < s.re} := by sorry
