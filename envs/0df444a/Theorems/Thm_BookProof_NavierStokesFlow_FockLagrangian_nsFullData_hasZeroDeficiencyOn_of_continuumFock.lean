-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_nsFullData_hasZeroDeficiencyOn_of_continuumFock
-- name    : BookProof.NavierStokesFlow.FockLagrangian.nsFullData_hasZeroDeficiencyOn_of_continuumFock
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:52:38.103497+00:00
-- url     : https://prove2.me/theorems/6ec32c9f-bdff-491a-b9cf-b269f7c923b7
-- title:
--   `BookProof.NavierStokesFlow.FockLagrangian.nsFullData_hasZeroDeficiencyOn_of_continuumFock` (d : FullEsa.NSFullData F) (μ : Measure Ω) {p q dr : Fin 3 → Ω → ℝ} {cf : Ω → ℝ} (hp : ∀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockParcels`.
--
--   `BookProof.NavierStokesFlow.FockLagrangian.nsFullData_hasZeroDeficiencyOn_of_continuumFock` (d : FullEsa.NSFullData F) (μ : Measure Ω) {p q dr : Fin 3 → Ω → ℝ} {cf : Ω → ℝ} (hp : ∀ i, Measurable (p i)) (hq : ∀ i, Measurable (q i)) (hd : ∀ i, Measurable (dr i)) (hc : Measurable cf) (force : Fin 3 → ℝ) {nu : ℝ} (hnu : 0 ≤ nu) (W : F ≃ₗᵢ[ℂ] Lp ℂ 2 (fockMeasure μ)) (hmap : ∀ x : d.D, W (x : F) ∈ (fockLagSymbols μ hp hq hd hc force hnu).data.D) (hsurj : ∀ y : (fockLagSymbols μ hp hq hd hc force hnu).data.D, ∃ x : d.D, W (x : F) = (y : Lp ℂ 2 (fockMeasure μ))) (hint : ∀ x : d.D, (((fockLagSymbols μ hp hq hd hc force hnu).data.hFull ⟨W (x : F), hmap x⟩ : (fockLagSymbols μ hp hq hd hc force hnu).data.D) : Lp ℂ 2 (fockMeasure μ)) = W ((d.hamiltonian x : F))) : HasZeroDeficiencyOn d.D d.hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockLagrangian.nsFullData_hasZeroDeficiencyOn_of_continuumFock`.

-- Generated from ChapterNavierStokesFockParcels.lean — theorem BookProof.NavierStokesFlow.FockLagrangian.nsFullData_hasZeroDeficiencyOn_of_continuumFock
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian


open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Ω : Type*} [MeasurableSpace Ω] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.FockLagrangian.nsFullData_hasZeroDeficiencyOn_of_continuumFock (d : FullEsa.NSFullData F)
    (μ : Measure Ω) {p q dr : Fin 3 → Ω → ℝ} {cf : Ω → ℝ} (hp : ∀ i, Measurable (p i))
    (hq : ∀ i, Measurable (q i)) (hd : ∀ i, Measurable (dr i)) (hc : Measurable cf)
    (force : Fin 3 → ℝ) {nu : ℝ} (hnu : 0 ≤ nu)
    (W : F ≃ₗᵢ[ℂ] Lp ℂ 2 (fockMeasure μ))
    (hmap : ∀ x : d.D, W (x : F) ∈ (fockLagSymbols μ hp hq hd hc force hnu).data.D)
    (hsurj : ∀ y : (fockLagSymbols μ hp hq hd hc force hnu).data.D,
      ∃ x : d.D, W (x : F) = (y : Lp ℂ 2 (fockMeasure μ)))
    (hint : ∀ x : d.D,
      (((fockLagSymbols μ hp hq hd hc force hnu).data.hFull ⟨W (x : F), hmap x⟩ :
        (fockLagSymbols μ hp hq hd hc force hnu).data.D) : Lp ℂ 2 (fockMeasure μ))
        = W ((d.hamiltonian x : F))) :
    HasZeroDeficiencyOn d.D d.hamiltonian := by sorry
