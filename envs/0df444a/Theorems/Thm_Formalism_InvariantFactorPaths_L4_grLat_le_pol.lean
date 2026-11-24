-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_grLat_le_pol
-- name    : Formalism.InvariantFactorPaths.L4.grLat_le_pol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:52.736698+00:00
-- url     : https://prove2.me/theorems/ae87b4be-42e8-420e-8a7f-c6a8f8d3dcc8
-- title:
--   L4: gr Lat le pol
-- statement:
--   The L4 construction uses the gr Lat le pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/PartnerDeterminantHolds.lean#L94-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/PartnerDeterminantHolds.lean#L94-L110

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementA
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem Formalism.InvariantFactorPaths.L4.grLat_le_pol (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ (Pol p r LLw).restrictScalars ℤ_[p] := by sorry
