-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_N3xM_S
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_N3xM_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:56.820796+00:00
-- url     : https://prove2.me/theorems/9279597f-8451-4b53-a772-d2d3972435db
-- title:
--   P: s1c2 N3x M S
-- statement:
--   The P construction uses the s1c2 N3x M S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L316-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L316-L328

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts

theorem Formalism.HermitianLatticeCounting.P.s1c2_N3xM_S (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (g s s' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) (hs' : s' ∈ Sset k r z') :
    formalDeterminantVectorOnGroup k r z z' (s * g * s') = s'⁻¹ *ᵥ formalDeterminantVectorOnGroup k r z z' g := by sorry
