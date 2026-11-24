-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_Fsum
-- name    : Formalism.InvariantFactorPaths.KP.LL.po_Fsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:43.136928+00:00
-- url     : https://prove2.me/theorems/1f4be7bc-acbb-4030-8821-4a45fc7f1a8c
-- title:
--   LL: po Fsum
-- statement:
--   The LL construction uses the po Fsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L15-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L15-L68

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.InvariantFactorPaths.KP.LL.po_Fsum {σ ι : Type} [DecidableEq ι]
    (Dc : ι → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]))
    (hcomm : ∀ a b, Commute (Dc a) (Dc b))
    (Λ : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hdiv : ∀ a k l, ∀ x ∈ Λ l, ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • (Dc a ^ k) x) ∈ Λ (l + k))
    (L n : ℕ) (hn : Nat.log p n ≤ L) (S : Finset ι) :
    ∀ j ≤ n, ∀ l, ∀ x ∈ Λ l,
      (((p : ℚ_[p]) ^ (S.card * L) * ((j.factorial : ℚ_[p]) ^ 2)⁻¹) • ((∑ c ∈ S, Dc c) ^ j) x) ∈ Λ (l + j) := by sorry
