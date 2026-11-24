-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_degreeOf_eq_zero_of_dvd
-- name    : Formalism.G0.DetDividesP.degreeOf_eq_zero_of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:48.990543+00:00
-- url     : https://prove2.me/theorems/b5b081b3-b138-4737-8ce1-d54157b0db44
-- title:
--   Det Divides P: degree Of eq zero of dvd
-- statement:
--   The Det Divides P construction uses the degree Of eq zero of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L312-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L312-L318

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

theorem Formalism.G0.DetDividesP.degreeOf_eq_zero_of_dvd {σ : Type} {p f : MvPolynomial σ K} (x : σ) (hpf : p ∣ f) (hf : f ≠ 0)
    (h : degreeOf x f = 0) : degreeOf x p = 0 := by sorry
