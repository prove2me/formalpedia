-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_proposition_4_2_ii
-- name    : DelayImpulse.Optimal.proposition_4_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:09.917578+00:00
-- url     : https://prove2.me/theorems/56c4e7e1-7a22-41e1-ad36-4c44442a85f7
-- title:
--   Proposition 4.2 ii), p. 7 — if ν ≤ ν′ are stopping times then Yₜ(ν, ξ) = Yₜ(ν′, ξ) for all t ≥ ν′, P-a.s.
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying a standard $d$-dimensional Brownian motion $B$, $(\mathcal F_t)_{t\ge0}$ is its natural filtration augmented by the $P$-null sets, and the data $(U,\Delta,r,k,\varphi,\gamma,h,L)$ satisfy the standing hypotheses of §3 and Assumption 3.1 ($U\subset\mathbb R^l$ finite and nonempty, $\Delta>0$, $r>0$, $k>0$, $\varphi\ge0$ on $U$, $L$ progressively measurable, $h$ measurable for $\mathcal P\otimes\mathcal B(\mathbb R^l)$ and $0\le h\le\gamma$ a.s.). $(Y^n,O^n)_n$ is any solution of the iterative scheme (4.4)–(4.6) and $Y=\lim_n Y^n$ (Proposition 4.2 i)). Let $(\nu,\xi)$ be an index and $\nu'$ a stopping time with $\nu\le\nu'$. Then, $P$-a.s.,
--   $$Y_t(\nu,\xi)=Y_t(\nu',\xi)\qquad\text{for all }t\ge\nu'.$$
--
--   After the later of the two starting times, the value does not remember when the reward started to accrue; this is what lets the scheme restart at each decision time.
--
--   **Formalization Note** The scheme is the predicate `IsScheme`: $Y^n$ and $O^n$ are adapted with continuous paths, $Y^0$ is given by (4.4), $O^{n}$ equals the right-hand side of (4.5) ii) a.s. at each $t$ (a pinned version of the optional projection), and $Y^{n}$ is the Snell envelope (4.6) of the reward with obstacle $O^n$; the reflected BSDE (4.5) i), iii) itself is not formalized. A process evaluated at the time $+\infty$ is $0$, and $e^{-r\cdot(+\infty)}=0$, which is the paper's convention $y_\infty=\lim_{t\to\infty}y_t$ for its processes. An index $(\nu,\xi)$ of the scheme is a stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable $\xi$ (p. 5). $Y=\lim_n Y^n$ is written as the pointwise supremum $\sup_n Y^n$.
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, p. 7, Proposition 4.2 ii)

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DelayImpulse.Optimal

theorem proposition_4_2_ii
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D)
    (Yn On : ℕ → Fam Ω l) (hS : IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On)
    (ν ν' : Ω → WithTop ℝ≥0) (ξ : Ω → Fin l → ℝ) (hξ : IsIndex (ReflectedBSDE.Existence.augmentedFiltration P hB) ν ξ)
    (hν' : IsStoppingTime (ReflectedBSDE.Existence.augmentedFiltration P hB) ν') (hνν' : ∀ ω, ν ω ≤ ν' ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ν' ω ≤ t → Ylim Yn ν ξ t ω = Ylim Yn ν' ξ t ω := by sorry
end DelayImpulse.Optimal
