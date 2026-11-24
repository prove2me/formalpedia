-- Prove2me | Theorems.Thm_Formalism_L2_Props_uniR_of_uniRT
-- name    : Formalism.L2.Props.uniR_of_uniRT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:46.819426+00:00
-- url     : https://prove2.me/theorems/04044a09-4503-46ed-be78-04bdb1ce920e
-- title:
--   Props: uni R of uni RT
-- statement:
--   The Props construction uses the uni R of uni RT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/AdelicCompactOpens/UniROfUniRT.lean#L41-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/AdelicCompactOpens/UniROfUniRT.lean#L41-L53

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLevel
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_GLintCompactOpen
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Props
open NumberField IsDedekindDomain Formalism.L2.NG ReciprocityTheory.Aut
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {L n}

theorem Formalism.L2.Props.uniR_of_uniRT {s : SplitPlace L} {r : ℕ} {h : GL (Fin n) (s.v.adicCompletion L⁺)} (hh : UniRT s r h) :
    UniR r h := by sorry
