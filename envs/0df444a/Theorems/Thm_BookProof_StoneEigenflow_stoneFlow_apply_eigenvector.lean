-- Prove2me | Theorems.Thm_BookProof_StoneEigenflow_stoneFlow_apply_eigenvector
-- name    : BookProof.StoneEigenflow.stoneFlow_apply_eigenvector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:18:02.794993+00:00
-- url     : https://prove2.me/theorems/0dcd3406-e8c4-4b2f-bd9f-223563a42fb3
-- title:
--   `BookProof.StoneEigenflow.stoneFlow_apply_eigenvector` {T : UnboundedSelfAdjoint F} {U : ℝ → (F →L[ℂ] F)} (hU : IsStoneFlow T U) {x : F} (hx : x ∈ T.domain) {lam : ℝ} (hev : T.op ⟨
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneEigenflow`.
--
--   `BookProof.StoneEigenflow.stoneFlow_apply_eigenvector` {T : UnboundedSelfAdjoint F} {U : ℝ → (F →L[ℂ] F)} (hU : IsStoneFlow T U) {x : F} (hx : x ∈ T.domain) {lam : ℝ} (hev : T.op ⟨x, hx⟩ = (lam : ℂ) • x) (t : ℝ) : U t x = Complex.exp (-(Complex.I * lam * t)) • x
--
--   Formalization note: Lean 4 identifier `BookProof.StoneEigenflow.stoneFlow_apply_eigenvector`.

-- Generated from ChapterStoneEigenflow.lean — theorem BookProof.StoneEigenflow.stoneFlow_apply_eigenvector
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterStoneEigenflow
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
open BookProof.StoneBridge
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.StoneEigenflow


open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.EsaClosure BookProof.FarisLavine
open BookProof.ChapterStoneResolvent BookProof.StoneBridge

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.StoneEigenflow.stoneFlow_apply_eigenvector {T : UnboundedSelfAdjoint F} {U : ℝ → (F →L[ℂ] F)}
    (hU : IsStoneFlow T U) {x : F} (hx : x ∈ T.domain) {lam : ℝ}
    (hev : T.op ⟨x, hx⟩ = (lam : ℂ) • x) (t : ℝ) :
    U t x = Complex.exp (-(Complex.I * lam * t)) • x := by sorry
