-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcdeg_degreeOf_aeval_le
-- name    : Formalism.GradedWeylDivisibility.lcdeg_degreeOf_aeval_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:07.579803+00:00
-- url     : https://prove2.me/theorems/30737e71-51fa-43b5-be41-81049070f6a4
-- title:
--   Graded Weyl Divisibility: lcdeg degree Of aeval le
-- statement:
--   The Graded Weyl Divisibility construction uses the lcdeg degree Of aeval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCdegLemmas.lean#L17-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCdegLemmas.lean#L17-L37

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCdegLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.lcdeg_degreeOf_aeval_le {σ τ R : Type*} [CommRing R] (f : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) (c : τ) (d : ℕ)
    (h : ∀ m ∈ p.support, ∑ v ∈ m.support, m v * degreeOf c (f v) ≤ d) :
    degreeOf c (aeval f p) ≤ d := by sorry
