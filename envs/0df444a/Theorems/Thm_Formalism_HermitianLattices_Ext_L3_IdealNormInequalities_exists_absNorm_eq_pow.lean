-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_exists_absNorm_eq_pow
-- name    : Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.exists_absNorm_eq_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:47.850436+00:00
-- url     : https://prove2.me/theorems/7a977688-efb2-4b1a-ba67-efe3bcc497ad
-- title:
--   Ideal Norm Inequalities: exists abs Norm eq pow
-- statement:
--   The Ideal Norm Inequalities construction uses the exists abs Norm eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFilterResCharLe.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFilterResCharLe.lean#L37-L48

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.exists_absNorm_eq_pow {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm P = resChar P ^ k := by sorry
