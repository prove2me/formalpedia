-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_mulD_comp_prime
-- name    : BookProof.NavierStokesFlow.FockLagrangian.mulD_comp_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T11:38:47.47641+00:00
-- url     : https://prove2.me/theorems/519a4b29-b66a-443a-81cb-c0522fa694e5
-- title:
--   BookProof.NavierStokesFlow.FockLagrangian.mulD_comp'
-- statement:
--   BookProof.NavierStokesFlow.FockLagrangian.mulD_comp'

-- Generated from ChapterNavierStokesFockLagrangian.lean — theorem BookProof.NavierStokesFlow.FockLagrangian.mulD_comp'
import Mathlib
import Definitions.Def_ChapterNavierStokesFockLagrangian
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian


open MeasureTheory



open FullEsa FockContinuum

variable {X : Type*} [MeasurableSpace X]

theorem BookProof.NavierStokesFlow.FockLagrangian.mulD_comp_prime (μ : Measure X) {g h₁ h₂ h : X → ℝ} (hh₁ : Measurable h₁)
    (hh₂ : Measurable h₂) (hh : Measurable h) (d₁ : DominatedOn μ g h₁)
    (d₂ : DominatedOn μ g h₂) (d : DominatedOn μ g h) (heq : ∀ x, h x = h₁ x * h₂ x) :
    (mulD μ hh₁ d₁).comp (mulD μ hh₂ d₂) = mulD μ hh d := by sorry
