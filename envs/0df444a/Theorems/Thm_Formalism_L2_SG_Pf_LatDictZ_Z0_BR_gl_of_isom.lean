-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_gl_of_isom
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.BR.gl_of_isom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:02.8858+00:00
-- url     : https://prove2.me/theorems/2928a7f7-d15c-49f5-9862-9aacac07e8e3
-- title:
--   BR: gl of isom
-- statement:
--   The BR construction uses the gl of isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/UnimodOfSelfDual.lean#L91-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/UnimodOfSelfDual.lean#L91-L127

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.BR
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.BR.gl_of_isom {J : Matrix (Fin n) (Fin n) E} (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hg : ∀ x y, hJ J (g x) (g y) = hJ J x y) :
    ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧ ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w := by sorry
