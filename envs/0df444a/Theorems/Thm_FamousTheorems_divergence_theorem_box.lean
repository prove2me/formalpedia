-- Prove2me | Theorems.Thm_FamousTheorems_divergence_theorem_box
-- name    : FamousTheorems.divergence_theorem_box
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:44.044352+00:00
-- url     : https://prove2.me/theorems/3ebd89f7-81dc-4ac6-b9b7-418f5863d9b1
-- title:
--   The divergence theorem (Gauss–Green) on a box
-- statement:
--   **The divergence theorem (Gauss–Green) on a box.** Let $[a,b]\subset\mathbb R^{n+1}$ be a closed box and $f:\mathbb R^{n+1}\to E^{n+1}$ a vector field with values in a Banach space $E$. Suppose $f$ is continuous on $[a,b]$, differentiable on the interior of the box outside a countable set, and its divergence $\operatorname{div}f=\sum_i\partial_if_i$ is integrable on $[a,b]$. Then
--   $$\int_{[a,b]}\operatorname{div}f=\sum_{i=0}^{n}\Big(\int_{\text{face }x_i=b_i}f_i-\int_{\text{face }x_i=a_i}f_i\Big).$$
--
--   This is the divergence theorem, the higher-dimensional form of the fundamental theorem of calculus. It is fundamental in vector calculus, physics (Gauss's law, conservation laws) and partial differential equations. Green's theorem in the plane is its two-dimensional case.
--
--   **Formalization note.** Mathlib's `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. Points are functions `Fin (n + 1) → ℝ`, and `f' x` is the derivative of `f` at `x`, so the divergence is $\sum_i f'(x)(e_i)_i$ with `Pi.single i 1` the basis vector $e_i$. The face $x_i=c$ is parametrised by `Fin n → ℝ` via `Fin.insertNth` into the box `Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove)`. The hypothesis allows a countable exceptional set where `f` need not be differentiable.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem divergence_theorem_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → E)
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → E)
    (s : Set (Fin (n + 1) → ℝ)) (hs : s.Countable) (Hc : ContinuousOn f (Set.Icc a b))
    (Hd : ∀ x ∈ (Set.univ.pi fun i => Set.Ioo (a i) (b i)) \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (Pi.single i 1) i) (Set.Icc a b)) :
    ∫ x in Set.Icc a b, ∑ i, f' x (Pi.single i 1) i =
      ∑ i : Fin (n + 1),
        ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f (i.insertNth (b i) x) i) -
          ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f (i.insertNth (a i) x) i) := by sorry

end FamousTheorems
