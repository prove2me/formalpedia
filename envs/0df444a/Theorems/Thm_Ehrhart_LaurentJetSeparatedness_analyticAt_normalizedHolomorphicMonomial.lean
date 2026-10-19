-- Prove2me | Theorems.Thm_Ehrhart_LaurentJetSeparatedness_analyticAt_normalizedHolomorphicMonomial
-- name    : Ehrhart.LaurentJetSeparatedness.analyticAt_normalizedHolomorphicMonomial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/4cbacfe3-9caf-4fbd-a4f8-2439e9978e89
-- title:
--   Ehrhart.LaurentJetSeparatedness.analyticAt_normalizedHolomorphicMonomial
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | EhrhartVolumeInequality | external Lean 4.33.1 validation; bundle SHA256 7150ea60aef8441515028279454832b05d0f964f3966505d147b2c1d8afe9763

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.LaurentJetSeparatedness
open Set Filter Module
open scoped BigOperators Topology

theorem Ehrhart.LaurentJetSeparatedness.analyticAt_normalizedHolomorphicMonomial {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (p : TorusCharacters.LogSpace n) :
    AnalyticAt ℂ
      (AdaptedBergmanBasis.normalizedHolomorphicMonomial
        K hk φ u) p := by sorry
