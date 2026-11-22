-- Prove2me | Theorems.Thm_ApproxIdentity_eLpNorm_haarConv_sub_lt
-- name    : ApproxIdentity.eLpNorm_haarConv_sub_lt
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T18:48:50.06554+00:00
-- url     : https://prove2.me/theorems/6f3c47f4-dc72-4da2-a6d5-c5cd994f9f6c
-- title:
--   Approximate identities on a locally compact group: $\|\psi_U*f-f\|_{L^p}\to0$ as $\operatorname{supp}\psi_U\to\{1\}$, for $f\in L^p(G)$, $1\le p<\infty$
-- statement:
--   **Approximate identities converge in $L^p(G)$, $1\le p<\infty$, for a locally compact group $G$.** Let $G$ be a locally compact Hausdorff group with a left Haar measure $\mu$ (a Radon measure). For a kernel $\psi$ and a function $f$ on $G$ write
--   $$(\psi*f)(x)=\int_G\psi(y)\,f(y^{-1}x)\,d\mu(y).$$
--   Call $\psi$ *admissible for a neighbourhood $U$ of the identity* if $\psi$ is continuous, compactly supported, $\psi\ge0$, $\operatorname{supp}\psi\subseteq U$ and $\int_G\psi\,d\mu=1$ (such $\psi$ exist for every $U$, by Urysohn's lemma; a family $(\psi_U)_U$ of them is an approximate identity).
--
--   Let $1\le p<\infty$ and $f\in L^p(G,\mu)$ (complex-valued). Then for every $\varepsilon>0$ there is a neighbourhood $U$ of the identity $1\in G$ such that
--   $$\|\psi*f-f\|_{L^p(G,\mu)}<\varepsilon\qquad\text{for every kernel }\psi\text{ admissible for }U.$$
--   Equivalently, $\psi_U*f\to f$ in $L^p$ for every approximate identity $(\psi_U)$ as $U$ shrinks to $\{1\}$; the group need not be abelian or unimodular (the kernel acts on the left, through left translations $f\mapsto f(y^{-1}\,\cdot)$, which are isometries of $L^p$ continuous in $y$).
--
--   This is the classical approximation of the identity by convolution operators in group algebras. Section 9.3 of the source constructs 'approximate units' — nets of convolution operators $A(\varphi)=\int_G\varphi(g)\rho_G(g,\cdot)\,d\mu_G(g)$ converging to the identity in the strong operator topology — on its Hardy–Sobolev spaces of an $\mathbb R_{>0}$-modulated group (Lemma 9.3.2.1); the statement above is the classical $L^p$ case of that mechanism.
--
--   **Formalization Note.** Left Haar measure is Mathlib's `μ.IsHaarMeasure` (left-invariant); the classical Haar measure is a Radon measure, which is `μ.Regular` (automatic for second-countable $G$ and for Mathlib's `haarMeasure`). The convolution is written out as a Bochner integral; for $\psi\in C_c(G)$ and $f\in L^p$ it converges absolutely for every $x$. The $L^p$ norm is `eLpNorm` (values in $[0,\infty]$). The approximate identity 'as $U\to\{1\}$' is encoded by the $\varepsilon$–$U$ formulation.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 419, §9.3 (approximate units: nets of convolution operators converging to the identity in the topology of simple convergence), and pp. 422–424, Lemma 9.3.2.1 and its proof

import Mathlib

open MeasureTheory Topology
open scoped ENNReal

set_option autoImplicit false

namespace ApproxIdentity

theorem eLpNorm_haarConv_sub_lt {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (f : G → ℂ) (hf : MemLp f p μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (1 : G), ∀ ψ : G → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      tsupport ψ ⊆ U → ∫ x, ψ x ∂μ = 1 →
      eLpNorm (fun x : G => (∫ y, (ψ y : ℂ) * f (y⁻¹ * x) ∂μ) - f x) p μ < ENNReal.ofReal ε := by
  sorry

end ApproxIdentity
