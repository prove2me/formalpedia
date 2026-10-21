-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_proposition_4_2_i
-- name    : DelayImpulse.Optimal.proposition_4_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:09.119268+00:00
-- url     : https://prove2.me/theorems/91af684d-fd5d-4567-a6be-b7684ce4ff2c
-- title:
--   Proposition 4.2 i), p. 6 — Yⁿ(ν, ξ) ↑ Y(ν, ξ), Y càdlàg and bounded by (4.15), and Y is the Snell envelope (4.13) with obstacle (4.14)
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying a standard $d$-dimensional Brownian motion $B$, $(\mathcal F_t)_{t\ge0}$ is its natural filtration augmented by the $P$-null sets, and the data $(U,\Delta,r,k,\varphi,\gamma,h,L)$ satisfy the standing hypotheses of §3 and Assumption 3.1 ($U\subset\mathbb R^l$ finite and nonempty, $\Delta>0$, $r>0$, $k>0$, $\varphi\ge0$ on $U$, $L$ progressively measurable, $h$ measurable for $\mathcal P\otimes\mathcal B(\mathbb R^l)$ and $0\le h\le\gamma$ a.s.). $(Y^n,O^n)_n$ is any solution of the iterative scheme (4.4)–(4.6) and $Y=\lim_n Y^n$ (Proposition 4.2 i)). For every index $(\nu,\xi)$:
--
--   1. almost surely, for every $t$, $n\mapsto Y^n_t(\nu,\xi)$ is nondecreasing and converges to $Y_t(\nu,\xi)$;
--   2. almost surely the paths of $Y(\nu,\xi)$ are càdlàg (right-continuous with left limits at every $t>0$);
--   3. **(4.15)** almost surely, for all $t\ge0$, $0\le Y_t(\nu,\xi)\le\frac{\gamma}{r}e^{-rt}$;
--   4. a limit obstacle $O$ for $Y$, i.e. a right-continuous adapted version of
--   $$O_t(\nu,\xi)=\mathbb E\Big[\int_t^{t+\Delta}e^{-rs}h(s,L_s+\xi)\mathbf 1_{[s\ge\nu]}ds\,\Big|\,\mathcal F_t\Big]+\max_{\beta\in U}\mathbb E\big[-e^{-r(t+\Delta)}\psi(\beta)+Y_{t+\Delta}(\nu,\xi+\beta)\,\big|\,\mathcal F_t\big]\quad(4.14),$$
--   exists, and for every such $O$ and every $t$,
--   $$Y_t(\nu,\xi)=\operatorname*{ess\,sup}_{\tau\in\mathcal T_t}\mathbb E\Big[\int_t^\tau e^{-rs}h(s,L_s+\xi)\mathbf 1_{[s\ge\nu]}ds+O_\tau(\nu,\xi)\,\Big|\,\mathcal F_t\Big]\quad(4.13).$$
--
--   The limit $Y$ is therefore itself the value of an optimal stopping problem whose obstacle is built from $Y$.
--
--   **Formalization Note** The scheme is the predicate `IsScheme`: $Y^n$ and $O^n$ are adapted with continuous paths, $Y^0$ is given by (4.4), $O^{n}$ equals the right-hand side of (4.5) ii) a.s. at each $t$ (a pinned version of the optional projection), and $Y^{n}$ is the Snell envelope (4.6) of the reward with obstacle $O^n$; the reflected BSDE (4.5) i), iii) itself is not formalized. A process evaluated at the time $+\infty$ is $0$, and $e^{-r\cdot(+\infty)}=0$, which is the paper's convention $y_\infty=\lim_{t\to\infty}y_t$ for its processes. An index $(\nu,\xi)$ of the scheme is a stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable $\xi$ (p. 5). $Y=\lim_n Y^n$ is written as the pointwise supremum $\sup_n Y^n$. The paper's hypothesis "$\xi$ an $\mathcal F_\nu$-measurable random variable" is read with the finiteness of $\xi$ that §4 requires of every index.
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, p. 6, Proposition 4.2 i), (4.13)–(4.14); p. 7, (4.15) in its proof

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DelayImpulse.Optimal

theorem proposition_4_2_i
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D)
    (Yn On : ℕ → Fam Ω l) (hS : IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On)
    (ν : Ω → WithTop ℝ≥0) (ξ : Ω → Fin l → ℝ) (hξ : IsIndex (ReflectedBSDE.Existence.augmentedFiltration P hB) ν ξ) :
    (∀ᵐ ω ∂P, ∀ t, Monotone (fun n => Yn n ν ξ t ω) ∧
      Tendsto (fun n => Yn n ν ξ t ω) atTop (𝓝 (Ylim Yn ν ξ t ω))) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ContinuousWithinAt (fun s => Ylim Yn ν ξ s ω) (Ici t) t ∧
      (0 < t → ∃ y, Tendsto (fun s => Ylim Yn ν ξ s ω) (𝓝[<] t) (𝓝 y))) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ Ylim Yn ν ξ t ω ∧
      Ylim Yn ν ξ t ω ≤ D.γ / D.r * Real.exp (-D.r * t)) ∧
    (∃ O : Fam Ω l, IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O) ∧
    (∀ O : Fam Ω l, IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O →
      ∀ t, IsSnellAt (ReflectedBSDE.Existence.augmentedFiltration P hB) P D ν ξ (O ν ξ) t (Ylim Yn ν ξ t)) := by sorry
end DelayImpulse.Optimal
