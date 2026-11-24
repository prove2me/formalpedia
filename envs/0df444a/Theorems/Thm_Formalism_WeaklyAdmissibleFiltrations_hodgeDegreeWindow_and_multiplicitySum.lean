-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_hodgeDegreeWindow_and_multiplicitySum
-- name    : Formalism.WeaklyAdmissibleFiltrations.hodgeDegreeWindow_and_multiplicitySum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:39:34.792145+00:00
-- url     : https://prove2.me/theorems/3e36de4b-686e-4273-ab5b-dd05a566eb47
-- title:
--   Weakly Admissible Filtrations: hodge Degree Window and multiplicity Sum
-- statement:
--   The Weakly Admissible Filtrations construction uses the hodge Degree Window and multiplicity Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/Window.lean#L62-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/Window.lean#L62-L62

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]

theorem Formalism.WeaklyAdmissibleFiltrations.hodgeDegreeWindow_and_multiplicitySum : THWindow ∧ DimSum := by sorry
