-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteNormFibres_sigma_eq_pow
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.sigma_eq_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:45:15.786068+00:00
-- url     : https://prove2.me/theorems/e0cbcce2-e6e0-4301-878c-cd30b7b86519
-- title:
--   Finite Norm Fibres: sigma eq pow
-- statement:
--   The Finite Norm Fibres construction uses the sigma eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardSumNormFibres.lean#L46-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardSumNormFibres.lean#L46-L111

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteNormFibres

theorem Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.sigma_eq_pow {k : Type*} [Field k] [Fintype k] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2) :
    ∀ x, σ x = x ^ q := by sorry
