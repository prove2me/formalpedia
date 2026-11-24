-- Prove2me | Theorems.Thm_Formalism_HN_HeightGram_gmat_eq
-- name    : Formalism.HN.HeightGram.gmat_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:37.238017+00:00
-- url     : https://prove2.me/theorems/5cf8699e-66aa-405e-ae60-4bf1f6b2c788
-- title:
--   Height Gram: gmat eq
-- statement:
--   The Height Gram construction uses the gmat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L165-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L165-L183

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable {P S : Type} [Fintype P] [DecidableEq P] [Fintype S] [DecidableEq S] {j : ℕ}

theorem Formalism.HN.HeightGram.gmat_eq (lam : P → S → ℂ) (G : P → Matrix (Fin j) (Fin j) ℂ) (eS : S ≃ P × Fin 2) :
    (gmat lam G).submatrix (Equiv.prodCongr eS.symm (Equiv.refl (Fin j)))
        (Equiv.prodCongr eS.symm (Equiv.refl (Fin j))) =
      (kroneckerMap (· * ·) (amat lam eS) (1 : Matrix (Fin j) (Fin j) ℝ))ᵀ * bmat G *
        kroneckerMap (· * ·) (amat lam eS) (1 : Matrix (Fin j) (Fin j) ℝ) := by sorry
