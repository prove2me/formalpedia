-- Prove2me | Theorems.Thm_EthierKurtz_ito_formula
-- name    : EthierKurtz.ito_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:46:02.807176+00:00
-- url     : https://prove2.me/theorems/3ce50ab9-1611-4ba3-b900-6388eec002bf
-- title:
--   Theorem 2.9 — time-dependent multidimensional Itô formula
-- statement:
--   For a continuous adapted finite-variation part V, a continuous local-martingale part M, and X = X₀ + V + M, every C¹ in time and C² in space test function satisfies the full change-of-variables identity with the time integral, integrals against V and M, and one-half the double sum of integrals against cross-variation. The theorem supplies continuous adapted versions of the integrals and bracket, with the identity holding almost surely at all times.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 5, Section 2, Theorem 2.9, printed p. 287 (PDF p. 296), equations (2.40)–(2.41); conventions printed pp. 279–280, 286 (PDF pp. 288–289, 295).

import Definitions.Def_EthierKurtz_IsSourceLocalMartingale
import Definitions.Def_EthierKurtz_HasCrossVariation
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_HasContinuousStieltjesIntegral
import Definitions.Def_EthierKurtz_HasContinuousMartingaleIntegral

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Full time-dependent multidimensional Ito formula for continuous local
martingales plus adapted finite variation. Derivative witnesses express exactly
C^{1,2}; the time derivative at zero is one-sided. All four terms are retained.
Integral/bracket witnesses are conclusions, not extra restrictions on X. -/
theorem ito_formula
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hcomplete : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N)
    (V M X : ℝ≥0 → Ω → Fin d → ℝ)
    (hVcont : ∀ ω i, Continuous (fun t => V t ω i))
    (hVadapt : ∀ i, Adapted ℱ (fun t ω => V t ω i))
    (hVbv : ∀ ω i T, BoundedVariationOn (fun t => V t ω i) (Set.Icc 0 T))
    (hVzero : ∀ ω i, V 0 ω i = 0)
    (hMcont : ∀ ω i, Continuous (fun t => M t ω i))
    (hMadapt : ∀ i, Adapted ℱ (fun t ω => M t ω i))
    (hMlocal : ∀ i, IsSourceLocalMartingale P ℱ (fun t ω => M t ω i))
    (hMzero : ∀ᵐ ω ∂P, ∀ i, M 0 ω i = 0)
    (hXinitial : Measurable[ℱ 0] (X 0))
    (hX : ∀ t ω i, X t ω i = X 0 ω i + V t ω i + M t ω i)
    (f ft : ℝ≥0 → (Fin d → ℝ) → ℝ)
    (fx : ℝ≥0 → (Fin d → ℝ) → Fin d → ℝ)
    (fxx : ℝ≥0 → (Fin d → ℝ) → Fin d → Fin d → ℝ)
    (hf : Continuous (fun z : ℝ≥0 × (Fin d → ℝ) => f z.1 z.2))
    (hft : Continuous (fun z : ℝ≥0 × (Fin d → ℝ) => ft z.1 z.2))
    (hfx : ∀ i, Continuous (fun z : ℝ≥0 × (Fin d → ℝ) => fx z.1 z.2 i))
    (hfxx : ∀ i j, Continuous (fun z : ℝ≥0 × (Fin d → ℝ) => fxx z.1 z.2 i j))
    (hdt : ∀ t x, HasDerivWithinAt (fun s : ℝ => f s.toNNReal x)
      (ft t x) (Set.Ici 0) t.val)
    (hdx : ∀ t x i, HasDerivAt (fun r => f t (Function.update x i r))
      (fx t x i) (x i))
    (hdxx : ∀ t x i j, HasDerivAt (fun r => fx t (Function.update x j r) i)
      (fxx t x i j) (x j)) :
    ∃ (A L : ℝ≥0 → Ω → Fin d → Fin d → ℝ)
      (J K : ℝ≥0 → Ω → Fin d → ℝ),
      (∀ i j, HasCrossVariation P (fun t ω => M t ω i)
        (fun t ω => M t ω j) (fun t ω => A t ω i j)) ∧
      (∀ ω i j, Continuous (fun t => A t ω i j)) ∧
      (∀ i j, Adapted ℱ (fun t ω => A t ω i j)) ∧
      (∀ ω i j T, BoundedVariationOn (fun t => A t ω i j) (Set.Icc 0 T)) ∧
      (∀ i, HasContinuousStieltjesIntegral (fun t ω => V t ω i)
        (fun t ω => fx t (X t ω) i) (fun t ω => K t ω i)) ∧
      (∀ i, HasContinuousMartingaleIntegral P ℱ (fun t ω => M t ω i)
        (fun t ω => fx t (X t ω) i) (fun t ω => J t ω i)) ∧
      (∀ i j, HasContinuousStieltjesIntegral (fun t ω => A t ω i j)
        (fun t ω => fxx t (X t ω) i j) (fun t ω => L t ω i j)) ∧
      (∀ᵐ ω ∂P, ∀ t, f t (X t ω) - f 0 (X 0 ω) =
        (∫ s in (0 : ℝ)..t.val, ft s.toNNReal (X s.toNNReal ω)) +
        (∑ i, K t ω i) + (∑ i, J t ω i) +
        (1 / 2 : ℝ) * ∑ i, ∑ j, L t ω i j) := by sorry
