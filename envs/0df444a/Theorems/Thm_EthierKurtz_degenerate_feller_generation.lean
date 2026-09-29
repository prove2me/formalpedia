-- Prove2me | Theorems.Thm_EthierKurtz_degenerate_feller_generation
-- name    : EthierKurtz.degenerate_feller_generation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:04:50.799798+00:00
-- url     : https://prove2.me/theorems/ec2c4ca0-114b-470b-a76d-0c921fcb9d55
-- title:
--   Theorem 2.5 — degenerate smooth-core Feller generation
-- statement:
--   A symmetric nonnegative covariance field with twice continuously differentiable entries and bounded second partials, together with globally Lipschitz drift, has the smooth compactly supported graph as a core for a conservative positive strongly continuous contraction semigroup, even when the covariance is degenerate or unbounded.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 2, Theorem 2.5, printed p. 373 (PDF p. 382); operator (1.15), printed p. 368 (PDF p. 377).

import Mathlib

open Filter
open scoped Topology ZeroAtInfty ContDiff NNReal

namespace EthierKurtz

/-- Possibly degenerate, unbounded diffusion coefficients with bounded second
partial derivatives and globally Lipschitz drift have a smooth compact core. -/
theorem degenerate_feller_generation (d : ℕ) [NeZero d]
    (a : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsym : ∀ x u v, inner ℝ (a x u) v = inner ℝ u (a x v))
    (hnonneg : ∀ x u, 0 ≤ inner ℝ u (a x u))
    (hsmooth : ∀ i j : Fin d,
      ContDiff ℝ 2 (fun x => (a x (EuclideanSpace.single j 1)) i))
    (hsecond : ∀ i j k l : Fin d, ∃ M : ℝ, ∀ x,
      |fderiv ℝ (fun y =>
        fderiv ℝ (fun z => (a z (EuclideanSpace.single j 1)) i) y
          (EuclideanSpace.single l 1)) x (EuclideanSpace.single k 1)| ≤ M)
    (hlipschitz : ∃ K : ℝ≥0, LipschitzWith K b) :
    let G := fun (f : EuclideanSpace ℝ (Fin d) → ℝ)
      (x : EuclideanSpace ℝ (Fin d)) =>
      (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
        (a x (EuclideanSpace.single j 1)) i *
          fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)) + fderiv ℝ f x (b x)
    let graph : Set (C₀(EuclideanSpace ℝ (Fin d), ℝ) ×
        C₀(EuclideanSpace ℝ (Fin d), ℝ)) :=
      {fg | ContDiff ℝ ∞ (fg.1 : EuclideanSpace ℝ (Fin d) → ℝ) ∧
        HasCompactSupport (fg.1 : EuclideanSpace ℝ (Fin d) → ℝ) ∧
        ∀ x, fg.2 x = G fg.1 x}
    let bpClosure := fun (H : Set (EuclideanSpace ℝ (Fin d) → ℝ × ℝ)) =>
      {f | ∀ S : Set (EuclideanSpace ℝ (Fin d) → ℝ × ℝ), H ⊆ S →
        (∀ (u : ℕ → EuclideanSpace ℝ (Fin d) → ℝ × ℝ)
          (v : EuclideanSpace ℝ (Fin d) → ℝ × ℝ),
          (∀ n, u n ∈ S) → (∃ M : ℝ, ∀ n x, ‖u n x‖ ≤ M) →
          (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x))) → v ∈ S) → f ∈ S}
    let A := closure graph
    (∀ f g₁ g₂, (f, g₁) ∈ A → (f, g₂) ∈ A → g₁ = g₂) ∧
    ∃ T : ℝ → C₀(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ]
        C₀(EuclideanSpace ℝ (Fin d), ℝ),
      T 0 = ContinuousLinearMap.id ℝ _ ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)) ∧
      (∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1) ∧
      (∀ f, Tendsto (fun t : ℝ => T t f) (𝓝[>] (0 : ℝ)) (𝓝 f)) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) ∧
      (fun _ => (1, 0)) ∈ bpClosure
        ((fun fg : C₀(EuclideanSpace ℝ (Fin d), ℝ) ×
          C₀(EuclideanSpace ℝ (Fin d), ℝ) => fun x => (fg.1 x, fg.2 x)) '' A) := by sorry
