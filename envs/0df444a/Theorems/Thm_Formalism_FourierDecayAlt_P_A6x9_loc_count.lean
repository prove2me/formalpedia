-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_loc_count
-- name    : Formalism.FourierDecayAlt.P.A6x9.loc_count
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:11.53126+00:00
-- url     : https://prove2.me/theorems/b0cea98d-bd1b-4cd6-9821-2fa8d0a0fe9f
-- title:
--   A6x9: loc count
-- statement:
--   The A6x9 construction uses the loc count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PadicChangeOfVariables.lean#L412-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PadicChangeOfVariables.lean#L412-L491

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)

theorem Formalism.FourierDecayAlt.P.A6x9.loc_count (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {m k k' i : ℕ} {si z0 z0i : K}
    (hs : ((m + 1 : ℕ) : K) * si = 1) (hk : (π : K) ^ k * si ∈ R) (hz0 : z0 * z0i = 1)
    (hk' : (π : K) ^ k' * z0i ∈ R) (T : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (hcr : IsCr R cr)
    (a : Kˣ) (ha : (a : K) * (T : K) = ((m + 1 : ℕ) : K) * z0 ^ m * (π : K) ^ (k + 1 + k' + i))
    (haR : ((a⁻¹ : Kˣ) : K) ∈ R) :
    {p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i)) ∧
      p.2 ^ (m + 1) = T * cr p.1}.Finite ∧
    ({p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i)) ∧
      p.2 ^ (m + 1) = T * cr p.1}.ncard : ℝ) = modK R (a : K) := by sorry
