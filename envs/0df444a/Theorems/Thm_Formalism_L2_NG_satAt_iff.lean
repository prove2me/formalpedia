-- Prove2me | Theorems.Thm_Formalism_L2_NG_satAt_iff
-- name    : Formalism.L2.NG.satAt_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:56.17635+00:00
-- url     : https://prove2.me/theorems/5685e2f6-3a8e-449f-b9e7-e4246a078d52
-- title:
--   NG: sat At iff
-- statement:
--   The NG construction uses the sat At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsRowLoc.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsRowLoc.lean#L25-L26

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAutLoc
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsRowLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
open Formalism Formalism.L2 Formalism.L2.NG
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {L n}
variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem Formalism.L2.NG.satAt_iff (π : AutRep L n) {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (α : Fin (n / 2) → ℂ) : SatAt π Dv α ↔ SatAtS π.S Dv α := by sorry
