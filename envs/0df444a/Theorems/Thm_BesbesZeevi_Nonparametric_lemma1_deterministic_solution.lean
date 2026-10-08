-- Prove2me | Theorems.Thm_BesbesZeevi_Nonparametric_lemma1_deterministic_solution
-- name    : BesbesZeevi.Nonparametric.lemma1_deterministic_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:30:14.723667+00:00
-- url     : https://prove2.me/theorems/76f1cbd0-d933-4fb1-97dd-7062451df63b
-- title:
--   Lemma 1 (solution of (5)): $p^D=\max\{p^u,p^c\}$ on $[0,T']$, then $p_\infty$
-- statement:
--   Let $x,T>0$ and $\lambda\in\mathcal L$. Let $p^u$ be any maximizer of the revenue rate $p\lambda(p)$ over $[\underline p,\overline p]$, and let $p^c$ be any minimizer of $|\lambda(p)-x/T|$ over $[\underline p,\overline p]$. Put
--
--   $$
--   p^D=\max\{p^u,p^c\},\qquad T'=\min\{T,\ x/\lambda(p^D)\}.
--   $$
--
--   Consider the price path that charges $p^D$ for $s\le T'$ and $p_\infty$ for $s>T'$. This path is feasible for the deterministic relaxation (5), and it attains the optimal value:
--
--   $$
--   J^D(x,T\mid\lambda)=p^D\lambda(p^D)\,T'.
--   $$
--
--   Algorithm 1 is built to estimate $p^D$.
--
--   **Formalization Note** Only the first sentence of Lemma 1 is formalized. The second, $J^\pi\le J^D$ for every admissible policy, needs the general class of non-anticipating policies and is not part of this mission. For members of the class $\lambda(p^D)>0$, so $x/\lambda(p^D)$ is a genuine quotient.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 27 (PDF 29), Lemma 1 (first assertion)

import Mathlib
import Definitions.Def_BesbesZeevi_Nonparametric_Model

open MeasureTheory

namespace BesbesZeevi.Nonparametric

/-- Lemma 1 (first assertion), p. 27: the solution of (5) is `p(s) = p^D := max{p^u, p^c}` for
`s ∈ [0, T']` and `p(s) = p_∞` for `s > T'`, where `p^u` maximizes `r(λ(p)) = p λ(p)` and `p^c`
minimizes `|λ(p) - x/T|` over `[p̲, p̄]`, and `T' = min{T, x/λ(p^D)}`. -/
theorem lemma1_deterministic_solution (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x)
    (hT : 0 < T) (lam : ℝ → ℝ) (hlam : L.Mem P lam) (pU pC : ℝ)
    (hpU : pU ∈ Set.Icc P.pl P.pu)
    (hpU_max : IsMaxOn (fun p => p * lam p) (Set.Icc P.pl P.pu) pU)
    (hpC : pC ∈ Set.Icc P.pl P.pu)
    (hpC_min : IsMinOn (fun p => |lam p - x / T|) (Set.Icc P.pl P.pu) pC) :
    FeasiblePath P lam x T
        (fun s => if s ≤ min T (x / lam (max pU pC)) then max pU pC else P.pinf) ∧
      pathRevenue lam T
          (fun s => if s ≤ min T (x / lam (max pU pC)) then max pU pC else P.pinf)
        = JD P lam x T ∧
      JD P lam x T = max pU pC * lam (max pU pC) * min T (x / lam (max pU pC)) := by sorry

end BesbesZeevi.Nonparametric
