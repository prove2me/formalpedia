-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_exists_injective_shift_of_orbZ
-- name    : Formalism.FourierDecayAlt.P.A5x9.exists_injective_shift_of_orbZ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:04.325177+00:00
-- url     : https://prove2.me/theorems/d62e67eb-b27f-4394-8ef4-8c81fda76884
-- title:
--   A5x9: exists injective shift of orb Z
-- statement:
--   The A5x9 construction uses the exists injective shift of orb Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1495-L1573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1495-L1573

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K) (k : ℕ)

theorem Formalism.FourierDecayAlt.P.A5x9.exists_injective_shift_of_orbZ (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w : Point K) (y)
    (σ : Matrix (Fin w.1.sum) (Fin w.1.sum) K) (hσ : IsPP R k σ) :
    ∃ S : Cos R w → Cos R w, Function.Injective S ∧ ∀ q, kap R k w q = y →
      kap R k w (S q) = y ∧ phase ψ (rep R (S q)) = phase ψ (rep R q) * ψ (sUp σ) ∧
      ∀ p, orbZ w (rep R q) = base R k w y * p →
        ∃ g, IsUpUni g ∧ IsInt R g ∧ orbZ w (rep R (S q)) = base R k w y * (σ * p) * g := by sorry
