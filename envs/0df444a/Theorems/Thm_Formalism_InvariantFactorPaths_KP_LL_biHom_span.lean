-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_biHom_span
-- name    : Formalism.InvariantFactorPaths.KP.LL.biHom_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:56.561367+00:00
-- url     : https://prove2.me/theorems/2debf202-5f80-40db-ab9f-43248fb86509
-- title:
--   LL: bi Hom span
-- statement:
--   The LL construction uses the bi Hom span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/BiHomPlus.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/BiHomPlus.lean#L51-L64

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_BiHomPlus
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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}
omit [NeZero r]

theorem Formalism.InvariantFactorPaths.KP.LL.biHom_span {r' : ℕ} {w e : Fin r' → BVar N r D.T.t} {a b : ℕ} {S : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])}
    (h : ∀ x ∈ S, BiHom w e a b x) : ∀ x ∈ Submodule.span ℤ_[p] S, BiHom w e a b x := by sorry
