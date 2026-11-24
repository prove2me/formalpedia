-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_mp
-- name    : Formalism.HermitianLatticeCounting.P.s5b7_mp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:09.904509+00:00
-- url     : https://prove2.me/theorems/0cff49f6-0ca9-4148-b03a-e805e3c29cd7
-- title:
--   P: s5b7 mp
-- statement:
--   The P construction uses the s5b7 mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L695-L704
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L695-L704

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

theorem Formalism.HermitianLatticeCounting.P.s5b7_mp (d r : ℕ)
    (Φ : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d))) :
    MeasurePreserving (fun a : Fin r → EuclideanSpace ℂ (Fin (d + 1)) =>
      ((fun b => (Φ (a b)).ofLp.1), (fun b => (Φ (a b)).ofLp.2))) volume volume := by sorry
