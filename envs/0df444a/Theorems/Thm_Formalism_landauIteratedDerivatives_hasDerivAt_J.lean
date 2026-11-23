-- Prove2me | Theorems.Thm_Formalism_landauIteratedDerivatives_hasDerivAt_J
-- name    : Formalism.landauIteratedDerivatives.hasDerivAt_J
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:50.649587+00:00
-- url     : https://prove2.me/theorems/0513d7df-3f9d-4e89-a5e6-839161107909
-- title:
--   landau Iterated Derivatives: has Deriv At J
-- statement:
--   The landau Iterated Derivatives construction uses the has Deriv At J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean#L79-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean#L79-L103

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
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
open Formalism.landauIteratedDerivatives

theorem Formalism.landauIteratedDerivatives.hasDerivAt_J (hMD : MellinDeriv) {H : ℝ → ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    {σc : ℝ} (hgood : ∀ σ, σc < σ → Good H σ) (n : ℕ) {z : ℂ} (hz : σc < z.re) :
    HasDerivAt (J H n) (J H (n + 1) z) z := by sorry
