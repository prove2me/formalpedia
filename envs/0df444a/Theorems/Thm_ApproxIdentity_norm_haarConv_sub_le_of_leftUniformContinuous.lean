-- Prove2me | Theorems.Thm_ApproxIdentity_norm_haarConv_sub_le_of_leftUniformContinuous
-- name    : ApproxIdentity.norm_haarConv_sub_le_of_leftUniformContinuous
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:48:50.920215+00:00
-- url     : https://prove2.me/theorems/c12ee11f-cb1d-4f56-aff7-91c1b217063c
-- title:
--   Approximate identities on a locally compact group: $\psi_U*f\to f$ uniformly for left uniformly continuous $f$
-- statement:
--   **Approximate identities converge uniformly on left uniformly continuous functions.** Let $G$ be a locally compact Hausdorff group with a left Haar measure $\mu$ (no regularity of $\mu$ is needed). For a kernel $\psi$ and a function $f$ on $G$ write
--   $$(\psi*f)(x)=\int_G\psi(y)\,f(y^{-1}x)\,d\mu(y).$$
--   Call $\psi$ *admissible for a neighbourhood $U$ of the identity* if $\psi$ is continuous, compactly supported, $\psi\ge0$, $\operatorname{supp}\psi\subseteq U$ and $\int_G\psi\,d\mu=1$ (such $\psi$ exist for every $U$, by Urysohn's lemma; a family $(\psi_U)_U$ of them is an approximate identity).
--
--   Let $f\colon G\to\mathbb C$ be left uniformly continuous, i.e. $\sup_{x\in G}|f(y^{-1}x)-f(x)|\to0$ as $y\to1$: for every $\delta>0$ there is a neighbourhood $V$ of $1$ with $|f(y^{-1}x)-f(x)|\le\delta$ for all $y\in V$ and all $x\in G$. Then for every $\varepsilon>0$ there is a neighbourhood $U$ of $1$ such that
--   $$\sup_{x\in G}|(\psi*f)(x)-f(x)|\le\varepsilon\qquad\text{for every kernel }\psi\text{ admissible for }U,$$
--   i.e. $\psi_U*f\to f$ uniformly on $G$ for every approximate identity $(\psi_U)$. (No boundedness of $f$ is needed; left uniform continuity already makes $f$ continuous, so $\psi*f$ is defined everywhere.)
--
--   Together with `ApproxIdentity.eLpNorm_haarConv_sub_lt` (convergence in $L^p$, $1\le p<\infty$) this is the classical approximate-identity theorem for group algebras, the model for the approximate units of §9.3 of the source (Lemma 9.3.2.1), where convolution operators $A(\varphi)$ by kernels concentrating at the identity converge strongly to the identity.
--
--   **Formalization Note.** Left Haar measure is `μ.IsHaarMeasure`. The convolution is written out as a Bochner integral; it is the integral of a continuous compactly supported function, so no junk value occurs. Left uniform continuity is spelled out with neighbourhoods of $1$. Unlike `ApproxIdentity.eLpNorm_haarConv_sub_lt`, no `μ.Regular` hypothesis is assumed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 419, §9.3 (approximate units: nets of convolution operators converging to the identity in the topology of simple convergence), and pp. 422–424, Lemma 9.3.2.1 and its proof

import Mathlib

open MeasureTheory Topology
open scoped ENNReal

set_option autoImplicit false

namespace ApproxIdentity

theorem norm_haarConv_sub_le_of_leftUniformContinuous {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ)
    (hf : ∀ δ : ℝ, 0 < δ → ∃ V ∈ 𝓝 (1 : G), ∀ y ∈ V, ∀ x : G, ‖f (y⁻¹ * x) - f x‖ ≤ δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (1 : G), ∀ ψ : G → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      tsupport ψ ⊆ U → ∫ x, ψ x ∂μ = 1 →
      ∀ x : G, ‖(∫ y, (ψ y : ℂ) * f (y⁻¹ * x) ∂μ) - f x‖ ≤ ε := by sorry

end ApproxIdentity
