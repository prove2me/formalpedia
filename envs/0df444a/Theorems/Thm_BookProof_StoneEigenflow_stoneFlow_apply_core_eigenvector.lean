-- Prove2me | Theorems.Thm_BookProof_StoneEigenflow_stoneFlow_apply_core_eigenvector
-- name    : BookProof.StoneEigenflow.stoneFlow_apply_core_eigenvector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:47:41.898674+00:00
-- url     : https://prove2.me/theorems/23a9b729-5e87-429a-b9fc-3503f9841c8f
-- title:
--   `BookProof.StoneEigenflow.stoneFlow_apply_core_eigenvector` {D : Submodule ℂ F} {Hc : D →ₗ[ℂ] F} {T : UnboundedSelfAdjoint F} {U : ℝ → (F →L[ℂ] F)} (hext : IsSelfAdjointExtension H
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneEigenflow`.
--
--   `BookProof.StoneEigenflow.stoneFlow_apply_core_eigenvector` {D : Submodule ℂ F} {Hc : D →ₗ[ℂ] F} {T : UnboundedSelfAdjoint F} {U : ℝ → (F →L[ℂ] F)} (hext : IsSelfAdjointExtension Hc T.op) (hU : IsStoneFlow T U) (x : D) {lam : ℝ} (hx : Hc x = (lam : ℂ) • (x : F)) (t : ℝ) : U t (x : F) = Complex.exp (-(Complex.I * lam * t)) • (x : F)
--
--   Formalization note: Lean 4 identifier `BookProof.StoneEigenflow.stoneFlow_apply_core_eigenvector`.

-- Generated from ChapterStoneEigenflow.lean — theorem BookProof.StoneEigenflow.stoneFlow_apply_core_eigenvector
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterStoneEigenflow
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.StoneBridge
open BookProof.StoneEigenflow


open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.EsaClosure BookProof.FarisLavine
open BookProof.ChapterStoneResolvent BookProof.StoneBridge

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.StoneEigenflow.stoneFlow_apply_core_eigenvector {D : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {T : UnboundedSelfAdjoint F} {U : ℝ → (F →L[ℂ] F)}
    (hext : IsSelfAdjointExtension Hc T.op) (hU : IsStoneFlow T U) (x : D) {lam : ℝ}
    (hx : Hc x = (lam : ℂ) • (x : F)) (t : ℝ) :
    U t (x : F) = Complex.exp (-(Complex.I * lam * t)) • (x : F) := by sorry
