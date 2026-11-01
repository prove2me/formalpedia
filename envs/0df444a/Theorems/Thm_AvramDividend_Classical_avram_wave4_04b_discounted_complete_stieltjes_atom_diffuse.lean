-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_discounted_complete_stieltjes_atom_diffuse
-- name    : AvramDividend.Classical.avram_wave4_04b_discounted_complete_stieltjes_atom_diffuse
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:38:33.356979+00:00
-- url     : https://prove2.me/theorems/e3cd2e8f-094f-4f00-a136-bd4266968c8a
-- title:
--   Exact discounted finite-horizon dividend reward equals every right atom plus the entire diffuse Stieltjes reward
-- statement:
--   For any actual adapted increasing Avram dividend control D and any finite closed horizon [0,T], the complete discounted Stieltjes payment integral equals a countable sum over the right-payment atomic times, plus a residual Stieltjes integral against a measure without singleton atoms. This is an exact equality in ENNReal for every real discount parameter q, with the atom at zero and the final atom at T included, and retains every absolutely continuous and singular-continuous payment in the diffuse term. The atomic coefficient is the singleton mass of the actual dividend measure, identified by the already Proved rightLimit-minus-D singleton theorem. No atom-only concentration assumption is imposed.
-- source:
--   Finite-measure restriction from exact Avram closed-horizon dividend mass, canonical generic atomic/diffuse decomposition and Mathlib Lebesgue lintegral add/sum/smul/Dirac lemmas. Foundational full Stieltjes reward calculation, not an Itô–Meyer stochastic chain rule.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_exists_atomic_diffuse_decomposition

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_discounted_complete_stieltjes_atom_diffuse
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
      (∑' t : A,
        μ {(t : ℝ)} * ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) +
      (∫⁻ s : ℝ,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) := by sorry
