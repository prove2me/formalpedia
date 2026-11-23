-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_algHom_det_of
-- name    : Formalism.GradedWeylDivisibility.algHom_det_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:09.478083+00:00
-- url     : https://prove2.me/theorems/35e9d81b-7052-4215-b845-b5ef42c782a4
-- title:
--   Graded Weyl Divisibility: alg Hom det of
-- statement:
--   The Graded Weyl Divisibility construction uses the alg Hom det of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetMinor.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetMinor.lean#L51-L55

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
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

theorem Formalism.GradedWeylDivisibility.algHom_det_of {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) {s : ℕ} (M : Fin s → Fin s → A) :
    φ (Matrix.of M).det = (Matrix.of fun p q => φ (M p q)).det := by sorry
