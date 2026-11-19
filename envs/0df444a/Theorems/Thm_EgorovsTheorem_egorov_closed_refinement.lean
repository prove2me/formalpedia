-- Prove2me | Theorems.Thm_EgorovsTheorem_egorov_closed_refinement
-- name    : EgorovsTheorem.egorov_closed_refinement
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T19:07:29.48401+00:00
-- url     : https://prove2.me/theorems/15f0a9e6-7643-4375-a390-416b1530533d
-- title:
--   Egorov's theorem: closed set of uniform convergence on $\mathbb{R}^n$
-- statement:
--   Egorov's theorem on $\mathbb R^n$ with a closed set of uniform convergence — the refinement stated in the MathWorld entry. Let $n\in\mathbb N$, let $E\subseteq\mathbb R^n$ be measurable for the Borel or the Lebesgue σ-algebra, with Lebesgue measure $\mathrm{vol}(E)<\infty$, and let $(f_k)$ be extended-real-valued functions on $E$, each measurable (for the corresponding σ-algebra) and finite almost everywhere on $E$, converging almost everywhere on $E$ to a finite limit $g$. Then for every $\varepsilon>0$ there exists a closed set $A\subseteq E$ with
--   $$\mathrm{vol}(E\setminus A)<\varepsilon$$
--   such that $(f_k)$ converges uniformly to $g$ on $A$, in the same $\varepsilon$-$N$ sense as the main theorem: for every $\delta>0$ there is $N$ with $g(x)-\delta<f_k(x)<g(x)+\delta$ for all $k\ge N$ and all $x\in A$.
--
--   This is the second assertion of the MathWorld entry: when $X=\mathbb R^n$ and the σ-algebra is the class of Borel sets or the class of Lebesgue measurable sets, the set $A$ of the main theorem can be chosen closed. It strengthens the general theorem by adding topological regularity of the retained set, while specializing to Lebesgue measure on $\mathbb R^n$.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and the measure is `volume` (Lebesgue measure), the standard reading of the entry. `NullMeasurableSet E volume` covers both σ-algebra cases (Borel sets and sets in the Lebesgue completion); `AEMeasurable (f k) (volume.restrict E)` expresses Lebesgue measurability of the functions, which every Borel-measurable function satisfies. The conclusion asserts `IsClosed A`; closed sets are Borel, so no separate measurability conjunct is needed. The case $n=0$ is allowed.
-- source:
--   https://mathworld.wolfram.com/EgorovsTheorem.html — MathWorld, "Egorov's Theorem" (entry contributed by Alexis Humphreys), second paragraph (closed-set refinement); the entry cites Wheeden & Zygmund, Measure and Integral: An Introduction to Real Analysis (Dekker, 1977).

import Mathlib

open MeasureTheory Filter Topology Set

namespace EgorovsTheorem

theorem egorov_closed_refinement
    (n : ℕ)
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : NullMeasurableSet E volume)
    (hμE : volume E < ⊤)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EReal)
    (hf : ∀ k, AEMeasurable (f k) (volume.restrict E))
    (hf_fin : ∀ k, ∀ᵐ x ∂(volume.restrict E), f k x ≠ ⊥ ∧ f k x ≠ ⊤)
    (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hconv : ∀ᵐ x ∂(volume.restrict E), g x ≠ ⊥ ∧ g x ≠ ⊤ ∧
      Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ∀ ε : ℝ, 0 < ε → ∃ A : Set (EuclideanSpace ℝ (Fin n)), A ⊆ E ∧ IsClosed A ∧
      volume (E \ A) < ENNReal.ofReal ε ∧
      ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ k ≥ N, ∀ x ∈ A,
        g x - (δ : EReal) < f k x ∧ f k x < g x + (δ : EReal) := by sorry

end EgorovsTheorem
