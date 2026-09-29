-- Prove2me | Theorems.Thm_EthierKurtz_two_type_branching_diffusion
-- name    : EthierKurtz.two_type_branching_diffusion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T07:16:41.745493+00:00
-- url     : https://prove2.me/theorems/8c94fd5e-6d12-4833-9d3d-902bbd4c0164
-- title:
--   Theorem 2.1 — two-type critical branching limits
-- statement:
--   For a critical continuous-time two-type branching process with positive rates, positive mean matrix, finite third offspring moments, a positive slow eigenvector and an opposite-sign fast eigenvector, the accelerated scaled slow and compensated fast modes converge jointly to the specified continuous diffusion; the uncompensated fast mode follows its exponentially decaying initial layer uniformly in probability; its positive-time integral converges to the fast diffusion increment; and the first population coordinate is uniformly reconstructed from the slow mode and that initial layer.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986 (held reprint 1986/2005). Chapter 9, Section 2, Theorem 2.1, printed p. 393 (PDF p. 402); model and conventions on printed pp. 392–393 (PDF pp. 401–402).

import Definitions.Def_EthierKurtz_IsTwoTypeBranching
import Definitions.Def_EthierKurtz_twoTypeMode
import Definitions.Def_EthierKurtz_IsContinuousDiffusionLaw

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators ContDiff

namespace EthierKurtz

/-- Two-type critical branching: joint diffusion limit, fast-mode decay,
integrated fast-mode limit, and first-population reconstruction. -/
theorem two_type_branching_diffusion
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (ρ : Fin 2 → Measure (ℕ × ℕ)) [∀ i, IsProbabilityMeasure (ρ i)]
    (hthird : ∀ i, Integrable (fun k : ℕ × ℕ => (k.1 : ℝ)^3) (ρ i) ∧
      Integrable (fun k : ℕ × ℕ => (k.2 : ℝ)^3) (ρ i))
    (m : Matrix (Fin 2) (Fin 2) ℝ)
    (hm : ∀ i, m i 0 = ∫ k, (k.1 : ℝ) ∂ρ i)
    (hm' : ∀ i, m i 1 = ∫ k, (k.2 : ℝ) ∂ρ i)
    (hmpos : ∀ i j, 0 < m i j)
    (ν μ : Fin 2 → ℝ) (η : ℝ) (hη : 0 < η)
    (hνpos : ∀ i, 0 < ν i) (hμsign : μ 0 * μ 1 < 0)
    (hν : ∀ i, ∑ j : Fin 2, rate i * (m i j - if i = j then 1 else 0) * ν j = 0)
    (hμ : ∀ i, ∑ j : Fin 2, rate i * (m i j - if i = j then 1 else 0) * μ j = -η * μ i)
    (z : Fin 2 → ℝ≥0)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z : ∀ n, ℝ≥0 → Ω n → ℕ × ℕ)
    (hZ : ∀ n, IsTwoTypeBranching rate ρ (P n) (Z n))
    (hinit : ∀ n w, Z n 0 w =
      (⌊((n + 1 : ℕ) : ℝ≥0) * z 0⌋₊, ⌊((n + 1 : ℕ) : ℝ≥0) * z 1⌋₊)) :
    let X := fun n => twoTypeMode ν n (Z n)
    let Y := fun n => twoTypeMode μ n (Z n)
    let W := fun n t w => Y n t w +
      ∫ s in (0 : ℝ)..(t : ℝ), (n + 1 : ℕ) * η * Y n s.toNNReal w
    let L := fun n t w => X n t w • EuclideanSpace.single (0 : Fin 2) 1 +
      W n t w • EuclideanSpace.single (1 : Fin 2) 1
    let v := fun i : Fin 2 => if i = 0 then ν else μ
    let α := fun (r i j : Fin 2) => ∫ k : ℕ × ℕ,
      (v i 0 * ((k.1 : ℝ) - if r = 0 then 1 else 0) +
        v i 1 * ((k.2 : ℝ) - if r = 1 then 1 else 0)) *
      (v j 0 * ((k.1 : ℝ) - if r = 0 then 1 else 0) +
        v j 1 * ((k.2 : ℝ) - if r = 1 then 1 else 0)) ∂ρ r
    let d := ν 0 * μ 1 - μ 0 * ν 1
    let a := fun i j => (rate 0 * μ 1 * α 0 i j - rate 1 * μ 0 * α 1 i j) / d
    let initial : EuclideanSpace ℝ (Fin 2) :=
      (ν 0 * z 0 + ν 1 * z 1) • EuclideanSpace.single 0 1 +
      (μ 0 * z 0 + μ 1 * z 1) • EuclideanSpace.single 1 1
    ∃ Q : Measure
      ({x : ℝ≥0 → EuclideanSpace ℝ (Fin 2) // Continuous x} ×
        (ℕ → {x : ℝ≥0 → EuclideanSpace ℝ (Fin 2) //
          (∀ t, ContinuousWithinAt x (Set.Ici t) t) ∧
          ∀ t : ℝ≥0, 0 < t → ∃ b, Tendsto x (𝓝[<] t) (𝓝 b)})),
      IsProbabilityMeasure Q ∧
      (∀ n, Measure.map (fun q => (q.2 n).val) Q =
        Measure.map (fun w t => L n t w) (P n)) ∧
      IsContinuousDiffusionLaw (fun x i j => x 0 * a i j) (fun _ => 0)
        (Measure.dirac initial) Q (fun t q => q.1.val t) ∧
      (∀ᵐ q ∂Q, ∀ t, 0 ≤ q.1.val t 0) ∧
      (∀ᵐ q ∂Q, ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T → ‖(q.2 n).val t - q.1.val t‖ < ε) ∧
      (∀ T : ℝ≥0, 0 < T → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => P n {w | ∃ t : ℝ≥0, t ≤ T ∧
          ε < |Y n t w - Y n 0 w * Real.exp (-(n + 1 : ℕ) * η * (t : ℝ))|})
          atTop (𝓝 0)) ∧
      (∀ t₁ t₂ : ℝ≥0, 0 < t₁ → t₁ < t₂ →
        ∀ f : BoundedContinuousFunction ℝ ℝ,
          Tendsto (fun n => ∫ w, f (∫ s in (t₁ : ℝ)..(t₂ : ℝ),
            (n + 1 : ℕ) * η * Y n s.toNNReal w) ∂P n)
            atTop (𝓝 (∫ q, f (q.1.val t₂ 1 - q.1.val t₁ 1) ∂Q))) ∧
      (∀ T : ℝ≥0, 0 < T → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => P n {w | ∃ t : ℝ≥0, t ≤ T ∧
          ε < |((Z n ((n + 1 : ℕ) * t) w).1 : ℝ) / (n + 1 : ℕ) -
            (μ 1 * X n t w - ν 1 * Y n 0 w *
              Real.exp (-(n + 1 : ℕ) * η * (t : ℝ))) / d|}) atTop (𝓝 0)) := by sorry
