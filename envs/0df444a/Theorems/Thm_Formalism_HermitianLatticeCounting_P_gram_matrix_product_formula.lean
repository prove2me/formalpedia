-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gram_matrix_product_formula
-- name    : Formalism.HermitianLatticeCounting.P.gram_matrix_product_formula
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:13.764875+00:00
-- url     : https://prove2.me/theorems/a10780a1-7790-4f51-9910-c3a1cbbf0852
-- title:
--   P: gram matrix product formula
-- statement:
--   The P construction uses the gram matrix product formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L992-L997
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L992-L997

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix InnerProductSpace
open scoped ComplexConjugate
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem Formalism.HermitianLatticeCounting.P.gram_matrix_product_formula : Formalism.HermitianLatticeCounting.ExpansionTerms.GramDetEqProdDistances := by sorry
