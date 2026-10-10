-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_gramWeyl_eq
-- name    : BookProof.YangMillsAbelianEsa.gramWeyl_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:52:41.657046+00:00
-- url     : https://prove2.me/theorems/f9237788-c6ea-4579-a3a4-1e9ff2e456d5
-- title:
--   `BookProof.YangMillsAbelianEsa.gramWeyl_eq` {d N : ℕ} (v : Fin N → Fin d → ℝ) (T : Fin d → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin d) ℂ)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianEsa`.
--
--   `BookProof.YangMillsAbelianEsa.gramWeyl_eq` {d N : ℕ} (v : Fin N → Fin d → ℝ) (T : Fin d → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin d) ℂ) : ∑ i : Fin d, ∑ j : Fin d, ((((1 / 2 : ℝ) * ∑ m : Fin N, v m i * v m j : ℝ)) : ℂ) • weylProd (T i) (T j) p = ((1 / 2 : ℝ) : ℂ) • ∑ m : Fin N, (∑ i : Fin d, ((v m i : ℝ) : ℂ) • T i) ((∑ i : Fin d, ((v m i : ℝ) : ℂ) • T i) p)
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianEsa.gramWeyl_eq`.

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.gramWeyl_eq
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.YangMillsAbelianEsa



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

theorem BookProof.YangMillsAbelianEsa.gramWeyl_eq {d N : ℕ} (v : Fin N → Fin d → ℝ)
    (T : Fin d → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    ∑ i : Fin d, ∑ j : Fin d,
        ((((1 / 2 : ℝ) * ∑ m : Fin N, v m i * v m j : ℝ)) : ℂ) • weylProd (T i) (T j) p
      = ((1 / 2 : ℝ) : ℂ) • ∑ m : Fin N,
          (∑ i : Fin d, ((v m i : ℝ) : ℂ) • T i) ((∑ i : Fin d, ((v m i : ℝ) : ℂ) • T i) p) := by sorry
