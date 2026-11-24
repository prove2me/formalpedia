-- Prove2me | Theorems.Thm_Formalism_SLP_P_bmat_eq_of_decomp
-- name    : Formalism.SLP.P.bmat_eq_of_decomp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:11.150434+00:00
-- url     : https://prove2.me/theorems/a6f84517-8063-41c3-8d84-e18b3488f78b
-- title:
--   P: bmat eq of decomp
-- statement:
--   The P construction uses the bmat eq of decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SesquilinearDeterminantHolds.lean#L81-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SesquilinearDeterminantHolds.lean#L81-L91

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Hadamard
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset ComplexConjugate
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]

theorem Formalism.SLP.P.bmat_eq_of_decomp (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) {m : ℕ} (e : Fin m → V₁) (f : Fin m → V₂)
    (A C : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → V₁) (w : Fin m → V₂)
    (hu : ∀ i, u i = ∑ k, A i k • e k) (hw : ∀ j, w j = ∑ l, C j l • f l) :
    (Matrix.of fun i j => B (u i) (w j)) = A * (Matrix.of fun k l => B (e k) (f l)) * Cᴴ := by sorry
