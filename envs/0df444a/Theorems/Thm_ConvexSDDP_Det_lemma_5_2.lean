-- Prove2me | Theorems.Thm_ConvexSDDP_Det_lemma_5_2
-- name    : ConvexSDDP.Det.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:05.742767+00:00
-- url     : https://prove2.me/theorems/8cfa3ed1-be08-436a-9491-1ac3b74b09de
-- title:
--   Lemma 5.2, p. 24 — for monotone $\alpha$-Lipschitz minorants on a compact set, $f(x^k)-f^k(x^k)\to0$ iff $f(x^k)-f^{k-\kappa}(x^k)\to0$
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$ be compact, $f:\mathbb R^d\to\mathbb R$ convex, $\alpha\ge0$, and $(f^k)_{k\in\mathbb N}$ a sequence of convex $\alpha$-Lipschitz functions $\mathbb R^d\to\mathbb R$. Fix an integer $\kappa\ge0$ and suppose
--   $$f^{k-\kappa}(x)\le f^k(x)\le f(x)\qquad\text{for all }x\in\mathcal X$$
--   (the left inequality for $k\ge\kappa$, the right one for all $k$). Then for every sequence $(x^k)$ in $\mathcal X$,
--   $$\lim_{k\to\infty}f(x^k)-f^k(x^k)=0\iff\lim_{k\to\infty}f(x^k)-f^{k-\kappa}(x^k)=0.$$
--
--   In the proof of Theorem 2.1 it is applied with $\kappa=1$, $f=V_{t+1}$ and $f^k=V^k_{t+1}$ to pass from the current approximation to the previous one (p. 12).
--
--   **Formalization Note** "For any integer $\kappa$" is a fixed $\kappa\in\mathbb N$. In Lean `k - κ` is truncated subtraction, which differs from the page only for $k<\kappa$; the monotonicity hypothesis is required only for $k\ge\kappa$ and no limit sees finitely many indices. The functions are real valued, as in the lemma; convexity is on all of $\mathbb R^d$ and the Lipschitz property is global (`LipschitzWith α`).
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 24, Lemma 5.2

import Mathlib
open Filter Topology

namespace ConvexSDDP.Det

theorem lemma_5_2 {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (fk : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (α : NNReal)
    (hfk : ∀ k, ConvexOn ℝ Set.univ (fk k) ∧ LipschitzWith α (fk k))
    (κ : ℕ) (hmono : ∀ k, κ ≤ k → ∀ y ∈ X, fk (k - κ) y ≤ fk k y)
    (hle : ∀ k, ∀ y ∈ X, fk k y ≤ f y)
    (xs : ℕ → EuclideanSpace ℝ (Fin d)) (hxs : ∀ k, xs k ∈ X) :
    Tendsto (fun k => f (xs k) - fk k (xs k)) atTop (𝓝 0) ↔
      Tendsto (fun k => f (xs k) - fk (k - κ) (xs k)) atTop (𝓝 0) := by sorry

end ConvexSDDP.Det
