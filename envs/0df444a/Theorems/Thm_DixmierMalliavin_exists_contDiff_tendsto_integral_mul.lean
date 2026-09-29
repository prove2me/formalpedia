-- Prove2me | Theorems.Thm_DixmierMalliavin_exists_contDiff_tendsto_integral_mul
-- name    : DixmierMalliavin.exists_contDiff_tendsto_integral_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/4e017707-fc9e-5e9a-8564-1b8b9876e099
-- title:
--   One-variable Dixmier–Malliavin lemma in product form
-- statement:
--   Let $\delta$ be a real number with $0<\delta$. Then there exists a family of thresholds $\mathrm{thr}$, assigning to each $N\in\mathbb{N}$ a function $\mathrm{thr}\,N$ of an $N$-tuple of reals (indexed by `Fin N`), such that all values $\mathrm{thr}\,N\,p$ are positive, and with the following property. For every sequence $a:\mathbb{N}\to\mathbb{R}$ such that for all $N$ one has $0<a_N$ and $a_N\le \mathrm{thr}\,N\,(i\mapsto a_i)$, the threshold being evaluated at the tuple of the first $N$ terms of $a$, there exist functions $\varphi,\psi:\mathbb{R}\to\mathbb{C}$, both smooth ($C^\infty$ in the sense `ContDiff ℝ ⊤`), whose topological supports are contained in $[-\delta,\delta]$, such that for every smooth $F:\mathbb{R}\to\mathbb{C}$ and every sequence of functions $P:\mathbb{N}\to(\mathbb{R}\to\mathbb{C})$ satisfying $P_0=F$ and, for all $N$, $P_{N+1}(t)=P_N(t)-a_N^2\,P_N''(t)$ pointwise (the second derivative being the iterated `deriv`), the integrals $\int \varphi(t)P_N(t)\,dt$ with respect to Lebesgue measure converge, as $N\to\infty$, to $F(0)+\int \psi(t)F(t)\,dt$.
--
--   This is the one-variable analytic input to the Dixmier–Malliavin factorisation theorem: the Dirac mass at $0$ is realised, after testing against a smooth function, as a limit of the finite-order differential operators $\prod_{N}(1-a_N^2\,d^2/dt^2)$ applied to it, up to a smooth compactly supported remainder $\psi$, with $\varphi$ and $\psi$ supported in an arbitrarily small interval $[-\delta,\delta]$. It is used by [`DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add`](thm.html#DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add), which transports the statement to the setting of smooth vectors in a representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.lean

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem DixmierMalliavin.exists_contDiff_tendsto_integral_mul (δ : ℝ) (hδ : 0 < δ) :
    ∃ thr : (N : ℕ) → (Fin N → ℝ) → ℝ, (∀ N p, 0 < thr N p) ∧
      ∀ a : ℕ → ℝ, (∀ N, 0 < a N ∧ a N ≤ thr N (fun i : Fin N => a i)) →
        ∃ φ ψ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
          tsupport φ ⊆ Set.Icc (-δ) δ ∧ tsupport ψ ⊆ Set.Icc (-δ) δ ∧
          ∀ F : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → ∀ P : ℕ → ℝ → ℂ, P 0 = F →
            (∀ N, P (N + 1) = fun t => P N t - (((a N) ^ 2 : ℝ) : ℂ) * deriv (deriv (P N)) t) →
              Filter.Tendsto (fun N : ℕ => ∫ t, φ t * P N t) Filter.atTop
                (nhds (F 0 + ∫ t, ψ t * F t)) := by sorry
