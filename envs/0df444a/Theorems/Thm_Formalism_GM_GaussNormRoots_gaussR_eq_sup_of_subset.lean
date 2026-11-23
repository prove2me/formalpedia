-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_gaussR_eq_sup_of_subset
-- name    : Formalism.GM.GaussNormRoots.gaussR_eq_sup_of_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:33.128361+00:00
-- url     : https://prove2.me/theorems/0ee15b4d-8a61-4e63-8f82-4a431483ce2a
-- title:
--   Gauss Norm Roots: gauss R eq sup of subset
-- statement:
--   The Gauss Norm Roots construction uses the gauss R eq sup of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L12-L20

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
open Formalism.GM.GaussNormRoots
variable {K : Type} [NormedField K]

theorem Formalism.GM.GaussNormRoots.gaussR_eq_sup_of_subset (ρ : NNReal) (P : K[X]) (s : Finset ℕ) (hs : P.support ⊆ s) :
    gaussR ρ P = s.sup (fun k => ‖P.coeff k‖₊ * ρ ^ k) := by sorry
