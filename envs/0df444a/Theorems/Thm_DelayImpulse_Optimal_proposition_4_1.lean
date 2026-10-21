-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_proposition_4_1
-- name    : DelayImpulse.Optimal.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:02.498948+00:00
-- url     : https://prove2.me/theorems/a1207817-582f-4aae-ae26-0a020bfc2e9e
-- title:
--   Proposition 4.1, p. 5 — the scheme (4.4)–(4.6) is well-posed; 0 ≤ Yⁿₜ ≤ (γ/r)e^{−rt} (4.7) and Yⁿ ≤ Yⁿ⁺¹ (4.8)
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying a standard $d$-dimensional Brownian motion $B$, $(\mathcal F_t)_{t\ge0}$ is its natural filtration augmented by the $P$-null sets, and the data $(U,\Delta,r,k,\varphi,\gamma,h,L)$ satisfy the standing hypotheses of §3 and Assumption 3.1 ($U\subset\mathbb R^l$ finite and nonempty, $\Delta>0$, $r>0$, $k>0$, $\varphi\ge0$ on $U$, $L$ progressively measurable, $h$ measurable for $\mathcal P\otimes\mathcal B(\mathbb R^l)$ and $0\le h\le\gamma$ a.s.).
--
--   1. **Well-posedness.** The scheme (4.4)–(4.6) has a solution $(Y^n,O^n)_n$, and any two solutions have indistinguishable $Y^n(\nu,\xi)$ for every $n$ and every index $(\nu,\xi)$.
--   2. **(4.7)** For every solution, every $n$ and index $(\nu,\xi)$, almost surely, for all $t\ge0$,
--   $$0\le Y^n_t(\nu,\xi)\le\frac{\gamma}{r}e^{-rt}.$$
--   3. **(4.8)** Almost surely, for all $t\ge0$, $Y^n_t(\nu,\xi)\le Y^{n+1}_t(\nu,\xi)$.
--
--   This makes the scheme a well-defined increasing, uniformly bounded sequence, so its limit $Y$ exists.
--
--   **Formalization Note** The scheme is the predicate `IsScheme`: $Y^n$ and $O^n$ are adapted with continuous paths, $Y^0$ is given by (4.4), $O^{n}$ equals the right-hand side of (4.5) ii) a.s. at each $t$ (a pinned version of the optional projection), and $Y^{n}$ is the Snell envelope (4.6) of the reward with obstacle $O^n$; the reflected BSDE (4.5) i), iii) itself is not formalized. A process evaluated at the time $+\infty$ is $0$, and $e^{-r\cdot(+\infty)}=0$, which is the paper's convention $y_\infty=\lim_{t\to\infty}y_t$ for its processes. An index $(\nu,\xi)$ of the scheme is a stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable $\xi$ (p. 5). $Y=\lim_n Y^n$ is written as the pointwise supremum $\sup_n Y^n$. The Snell representation (4.6), which the paper proves from the reflected BSDE (4.5), is here part of the definition of the scheme, so "well-posed" becomes existence and uniqueness of a solution of the scheme.
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, p. 5, Proposition 4.1, (4.6)–(4.8)

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DelayImpulse.Optimal

theorem proposition_4_1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D) :
    (∃ Yn On : ℕ → Fam Ω l, IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On) ∧
    (∀ Yn On Yn' On' : ℕ → Fam Ω l, IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On →
      IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn' On' →
      ∀ n ν ξ, IsIndex (ReflectedBSDE.Existence.augmentedFiltration P hB) ν ξ → ∀ᵐ ω ∂P, ∀ t, Yn n ν ξ t ω = Yn' n ν ξ t ω) ∧
    (∀ Yn On : ℕ → Fam Ω l, IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On →
      ∀ n ν ξ, IsIndex (ReflectedBSDE.Existence.augmentedFiltration P hB) ν ξ →
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ Yn n ν ξ t ω ∧
          Yn n ν ξ t ω ≤ D.γ / D.r * Real.exp (-D.r * t)) ∧
        (∀ᵐ ω ∂P, ∀ t, Yn n ν ξ t ω ≤ Yn (n + 1) ν ξ t ω)) := by sorry
end DelayImpulse.Optimal
