-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_qgOuterFock_esa_farisLavine
-- name    : BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:46:46.294397+00:00
-- url     : https://prove2.me/theorems/e96770a1-ab5e-4538-80ca-d00998057fb3
-- title:
--   `BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine` (H : ∀ n : ℕ, (harmFried (n * 84)).dom →ₗ[ℂ] L2d (n * 84)) (hsym : ∀ n : ℕ, SymmetricOn (harmFried (n * 84)).dom (H n)) (hext
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine` (H : ∀ n : ℕ, (harmFried (n * 84)).dom →ₗ[ℂ] L2d (n * 84)) (hsym : ∀ n : ℕ, SymmetricOn (harmFried (n * 84)).dom (H n)) (hext : ∀ (n : ℕ) (p : polyGaussCore (d := n * 84)) (h : (p : L2d (n * 84)) ∈ (harmFried (n * 84)).dom), H n ⟨(p : L2d (n * 84)), h⟩ = qgSectorHam n p) (K c : ℝ) (hc : 0 ≤ c) (hrel : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom), ‖H n u‖ ≤ K * ‖(harmFried (n * 84)).op u + (u : L2d (n * 84))‖) (hcomm : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom), |commForm (H n) (harmFried (n * 84)).op u| ≤ c * quadForm (harmFried (n * 84)).op u) : EssentiallySelfAdjointOn qgOuterFriedDom (dsFibOp (fun n : ℕ => harmFried (n * 84)) H K hrel) ∧ ∀ x : qgOuterCore, ∃ h : (x : qgOuterFock) ∈ qgOuterFriedDom, dsFibOp (fun n : ℕ => harmFried (n * 84)) H K hrel ⟨(x : qgOuterFock), h⟩ = qgOuterHam x
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.DirectSumEsa
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL


open scoped ENNReal


open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HashimotoShiftInvert
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable (C : ∀ i, Comparison (G i))
variable (H : ∀ i, (C i).dom →ₗ[ℂ] G i)
variable {C H}

theorem BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine
    (H : ∀ n : ℕ, (harmFried (n * 84)).dom →ₗ[ℂ] L2d (n * 84))
    (hsym : ∀ n : ℕ, SymmetricOn (harmFried (n * 84)).dom (H n))
    (hext : ∀ (n : ℕ) (p : polyGaussCore (d := n * 84))
      (h : (p : L2d (n * 84)) ∈ (harmFried (n * 84)).dom),
      H n ⟨(p : L2d (n * 84)), h⟩ = qgSectorHam n p)
    (K c : ℝ) (hc : 0 ≤ c)
    (hrel : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom),
      ‖H n u‖ ≤ K * ‖(harmFried (n * 84)).op u + (u : L2d (n * 84))‖)
    (hcomm : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom),
      |commForm (H n) (harmFried (n * 84)).op u| ≤ c * quadForm (harmFried (n * 84)).op u) :
    EssentiallySelfAdjointOn qgOuterFriedDom
        (dsFibOp (fun n : ℕ => harmFried (n * 84)) H K hrel) ∧
      ∀ x : qgOuterCore, ∃ h : (x : qgOuterFock) ∈ qgOuterFriedDom,
        dsFibOp (fun n : ℕ => harmFried (n * 84)) H K hrel ⟨(x : qgOuterFock), h⟩
          = qgOuterHam x := by sorry
