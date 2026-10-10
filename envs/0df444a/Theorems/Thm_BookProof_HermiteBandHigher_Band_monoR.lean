-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_Band_monoR
-- name    : BookProof.HermiteBandHigher.Band.monoR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:00:33.160482+00:00
-- url     : https://prove2.me/theorems/2fb3ad51-bd4c-47ea-a344-adbde11811b6
-- title:
--   `BookProof.HermiteBandHigher.Band.monoR` {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r r' M : ℕ} {C : ℝ} {g : ℕ → ℝ} (hr : r ≤ r') (h : Band T r M C g) : Band...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.Band.monoR` {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r r' M : ℕ} {C : ℝ} {g : ℕ → ℝ} (hr : r ≤ r') (h : Band T r M C g) : Band T r' M C g
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.Band.monoR`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.Band.monoR
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.Band.monoR {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r r' M : ℕ}
    {C : ℝ} {g : ℕ → ℝ} (hr : r ≤ r') (h : Band T r M C g) : Band T r' M C g := by sorry
