-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_WeakCauchyRiemannOn_congr_ae
-- name    : BookProof.WeylCauchyRiemann.WeakCauchyRiemannOn.congr_ae
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:35:47.215783+00:00
-- url     : https://prove2.me/theorems/dac381d7-ecdb-4344-bb29-327a4036251d
-- title:
--   `BookProof.WeylCauchyRiemann.WeakCauchyRiemannOn.congr_ae` {f g : ℂ → ℂ} {U : Set ℂ} (hg : WeakCauchyRiemannOn g U) (hae : ∀ᵐ z : ℂ, z ∈ U → f z = g z) : WeakCauchyRiemannOn f U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.WeakCauchyRiemannOn.congr_ae` {f g : ℂ → ℂ} {U : Set ℂ} (hg : WeakCauchyRiemannOn g U) (hae : ∀ᵐ z : ℂ, z ∈ U → f z = g z) : WeakCauchyRiemannOn f U
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.WeakCauchyRiemannOn.congr_ae`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.WeakCauchyRiemannOn.congr_ae
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.WeakCauchyRiemannOn.congr_ae {f g : ℂ → ℂ} {U : Set ℂ}
    (hg : WeakCauchyRiemannOn g U) (hae : ∀ᵐ z : ℂ, z ∈ U → f z = g z) :
    WeakCauchyRiemannOn f U := by sorry
