-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_measurePreserving_pi_comp_prod
-- name    : Formalism.HermitianLatticeCounting.P.measurePreserving_pi_comp_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:53.476258+00:00
-- url     : https://prove2.me/theorems/6569c54f-e55b-4549-8d11-d6d2447ad6ce
-- title:
--   P: measure Preserving pi comp prod
-- statement:
--   The P construction uses the measure Preserving pi comp prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L684-L693
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L684-L693

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate

theorem Formalism.HermitianLatticeCounting.P.measurePreserving_pi_comp_prod {α β γ δ : Type*} [MeasureSpace α] [MeasureSpace β] [MeasureSpace γ]
    [MeasureSpace δ] [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)]
    [SigmaFinite (volume : Measure γ)] [SigmaFinite (volume : Measure δ)] (r : ℕ) (f : α → β)
    (g : β → γ × δ) (hf : MeasurePreserving f) (hg : MeasurePreserving g) :
    MeasurePreserving (fun a : Fin r → α =>
      ((fun b => (g (f (a b))).1), (fun b => (g (f (a b))).2))) volume volume := by sorry
