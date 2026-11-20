-- Prove2me | Theorems.Thm_EgorovsTheorem_egorov_theorem
-- name    : EgorovsTheorem.egorov_theorem
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T19:07:17.767645+00:00
-- url     : https://prove2.me/theorems/50e25481-272e-4d02-9397-9b13f535b1c4
-- title:
--   Egorov's theorem
-- statement:
--   Egorov's theorem, as stated in the MathWorld entry. Let $(X,\mathcal B,\mu)$ be a measure space and let $E\in\mathcal B$ be a measurable set with $\mu(E)<\infty$. Let $(f_k)_{k\in\mathbb N}$ be a sequence of extended-real-valued functions on $E$, each measurable on $E$ and finite almost everywhere on $E$, and suppose that $(f_k)$ converges almost everywhere on $E$ to a finite limit $g$. Then for every $\varepsilon>0$ there exists a measurable set $A\subseteq E$ with
--   $$\mu(E\setminus A)<\varepsilon$$
--   such that $(f_k)$ converges uniformly to $g$ on $A$: for every $\delta>0$ there is $N\in\mathbb N$ such that for all $k\ge N$ and all $x\in A$,
--   $$g(x)-\delta<f_k(x)<g(x)+\delta.$$
--   In particular $g$ is finite at every point of $A$, and $f_k$ is finite on $A$ for all $k\ge N$.
--
--   The theorem converts almost-everywhere convergence on a finite-measure set into uniform convergence after removing a set of arbitrarily small measure; it is a basic tool of real analysis, feeding the Vitali convergence theorem and Lusin's theorem.
--
--   **Formalization Note.** Functions take values in Lean's `EReal` ($[-\infty,+\infty]$); "finite" means $\neq\pm\infty$. The functions are defined on $X$ but only constrained on $E$; measurability is required on the subtype $E$ with its trace σ-algebra. The limit $g$ is a parameter constrained almost everywhere; its measurability is not assumed. Uniform convergence is expressed in the $\varepsilon$-$N$ order form above, equivalent to $|f_k(x)-g(x)|<\delta$ when $g(x)$ is finite, and forcing finiteness of $g$ and of the tail on $A$. Measurability of $A$ is made explicit: the source's $\mu(E\setminus A)$ presupposes it.
-- source:
--   https://mathworld.wolfram.com/EgorovsTheorem.html — MathWorld, "Egorov's Theorem" (entry contributed by Alexis Humphreys), main theorem paragraph (first paragraph); the entry cites Wheeden & Zygmund, Measure and Integral: An Introduction to Real Analysis (Dekker, 1977).

import Mathlib

open MeasureTheory Filter Topology Set

namespace EgorovsTheorem

theorem egorov_theorem
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (E : Set X) (hE : MeasurableSet E) (hμE : μ E < ⊤)
    (f : ℕ → X → EReal)
    (hf : ∀ k, Measurable (fun x : ↥E => f k ↑x))
    (hf_fin : ∀ k, ∀ᵐ x ∂(μ.restrict E), f k x ≠ ⊥ ∧ f k x ≠ ⊤)
    (g : X → EReal)
    (hconv : ∀ᵐ x ∂(μ.restrict E), g x ≠ ⊥ ∧ g x ≠ ⊤ ∧
      Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ∀ ε : ℝ, 0 < ε → ∃ A : Set X, A ⊆ E ∧ MeasurableSet A ∧
      μ (E \ A) < ENNReal.ofReal ε ∧
      ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ k ≥ N, ∀ x ∈ A,
        g x - (δ : EReal) < f k x ∧ f k x < g x + (δ : EReal) := by sorry

end EgorovsTheorem
