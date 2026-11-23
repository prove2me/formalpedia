-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_sum
-- name    : Formalism.FourierDecayAlt.P.Jx7.psd_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:57.511965+00:00
-- url     : https://prove2.me/theorems/f1024d20-63c2-44f5-8a70-5452656359fe
-- title:
--   Jx7: psd sum
-- statement:
--   The Jx7 construction uses the psd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L728-L738
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L728-L738

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder ComplexConjugate Matrix
variable {α : Type} {F : Finset α}

theorem Formalism.FourierDecayAlt.P.Jx7.psd_sum {ι : Type} (s : Finset ι) (k : ι → α → α → ℂ) (hk : ∀ i ∈ s, TB.PSDOn F (k i)) :
    TB.PSDOn F (fun x y => ∑ i ∈ s, k i x y) := by sorry
