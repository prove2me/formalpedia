-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_prod_toMultiset_X
-- name    : BookProof.HermiteBandHigher.prod_toMultiset_X
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:07:49.473977+00:00
-- url     : https://prove2.me/theorems/af3bf40e-a03d-468b-b7b0-36bfd67f1dee
-- title:
--   `BookProof.HermiteBandHigher.prod_toMultiset_X` (s : Fin d →₀ ℕ) : ((s.toMultiset.map (fun i => (X i : MvPolynomial (Fin d) ℂ))).prod) = s.prod fun i k => (X i : MvPolynomial (Fin
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.prod_toMultiset_X` (s : Fin d →₀ ℕ) : ((s.toMultiset.map (fun i => (X i : MvPolynomial (Fin d) ℂ))).prod) = s.prod fun i k => (X i : MvPolynomial (Fin d) ℂ) ^ k
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.prod_toMultiset_X`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.prod_toMultiset_X
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.prod_toMultiset_X (s : Fin d →₀ ℕ) :
    ((s.toMultiset.map (fun i => (X i : MvPolynomial (Fin d) ℂ))).prod)
      = s.prod fun i k => (X i : MvPolynomial (Fin d) ℂ) ^ k := by sorry
