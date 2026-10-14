-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_ymAbelian_positiveExtension_eq_closure
-- name    : BookProof.YangMillsAbelianEsa.ymAbelian_positiveExtension_eq_closure
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:42:05.224303+00:00
-- url     : https://prove2.me/theorems/38976c1a-7f6e-46f1-a2af-b9d89ef42f7d
-- title:
--   `BookProof.YangMillsAbelianEsa.ymAbelian_positiveExtension_eq_closure` {Dom : Submodule ℂ (L2d 99)} {A : Dom →ₗ[ℂ] L2d 99} (hA : IsPositiveSelfAdjointExtension (ymHamiltonian (core
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianEsa`.
--
--   `BookProof.YangMillsAbelianEsa.ymAbelian_positiveExtension_eq_closure` {Dom : Submodule ℂ (L2d 99)} {A : Dom →ₗ[ℂ] L2d 99} (hA : IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepPoly 99) 0) A) : Dom = clDom (ymHamiltonian (coreRepPoly 99) 0) ∧ ∀ (x : L2d 99) (h : x ∈ Dom) (h' : x ∈ clDom (ymHamiltonian (coreRepPoly 99) 0)), A ⟨x, h⟩ = clExt (ymHamiltonian (coreRepPoly 99) 0) polyGaussCore_dense (ymHamiltonian_symmetricOn (coreRepPoly 99) 0) ⟨x, h'⟩
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianEsa.ymAbelian_positiveExtension_eq_closure`.

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.ymAbelian_positiveExtension_eq_closure
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn
open BookProof.EsaClosure
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
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

theorem BookProof.YangMillsAbelianEsa.ymAbelian_positiveExtension_eq_closure {Dom : Submodule ℂ (L2d 99)}
    {A : Dom →ₗ[ℂ] L2d 99}
    (hA : IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepPoly 99) 0) A) :
    Dom = clDom (ymHamiltonian (coreRepPoly 99) 0) ∧
      ∀ (x : L2d 99) (h : x ∈ Dom) (h' : x ∈ clDom (ymHamiltonian (coreRepPoly 99) 0)),
        A ⟨x, h⟩ = clExt (ymHamiltonian (coreRepPoly 99) 0) polyGaussCore_dense
          (ymHamiltonian_symmetricOn (coreRepPoly 99) 0) ⟨x, h'⟩ := by sorry
