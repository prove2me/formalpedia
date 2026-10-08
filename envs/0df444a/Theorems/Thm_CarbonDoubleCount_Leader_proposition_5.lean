-- Prove2me | Theorems.Thm_CarbonDoubleCount_Leader_proposition_5
-- name    : CarbonDoubleCount.Leader.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:26.841308+00:00
-- url     : https://prove2.me/theorems/79f92872-8831-409b-a616-4e7846642153
-- title:
--   Proposition 5, p. 16 — with emission-contingent payments the carbon leader achieves z^E and induces e^E by the double-counting linear rule (12)
-- statement:
--   **Setting.** Firms $n\in\mathcal N$ choose abatement efforts $e_n\in[0,A]^{m_n}$; firm $n$'s profit $V_n(e_n)$ is differentiable, concave and componentwise decreasing on its box; each process $i\in\mathcal I$ has a footprint $f_i(e)$ that is differentiable, convex, componentwise decreasing and non-negative on $[0,A]^M$. The influence matrix $B$ has $b_{n,i}\in\{0,1\}$, with $b_{n,i}=1$ exactly when $\sum_j\partial f_i/\partial e_{n,j}<0$. One firm $N$, the carbon leader, pays for all emissions at price $p\ge 0$; the other firms have reservation profits $\bar\pi_n$.
--
--   **Statement.** Let $(g^E,e^E)$ be optimal for the effort-contracting problem $P_E$ (6)–(8), with optimal value $z^E$ and emissions $f^E=f(e^E)$, and suppose $e^E$ is interior. Let
--   $$g_n(f)=p\sum_{i\in\mathcal I}b_{n,i}f_i+k_n,\qquad k_n=V_n(e^E_n)-p\sum_{i\in\mathcal I}b_{n,i}f^E_i-\bar\pi_n\qquad(n\neq N). \qquad (12)$$
--   Then:
--   1. $(g,e^E)$ is feasible for the emission-contracting problem $P_F$ (9)–(11): every firm $n\ne N$ accepts, and $e^E_n$ is its best response to $g_n$;
--   2. the leader's profit (9) at $(g,e^E)$ equals $z^E$;
--   3. no feasible solution of $P_F$ has a larger profit, so $z^E$ is the optimal value of $P_F$ and $(g,e^E)$ is optimal for $P_F$.
--
--   So a carbon leader that can commit loses nothing when efforts are unobservable: it achieves its effort-contracting profit through a linear rule that charges each firm the full carbon price on every footprint the firm influences. Internally this double-counts emissions, since $\sum_{n\ne N}b_{n,i}$ firms pay $p$ per unit of process $i$, yet the total payment rule of the supply chain is footprint balanced.
--
--   **Formalization Note.** "Optimal" means feasible with a value at least that of every feasible solution; $z^E$ is the objective at the optimal pair. Two readings are disclosed: $b_{n,i}$ is a sign pattern that holds at every profile of the box, and $e^E$ is interior (the page's "A is a sufficiently large bound to guarantee interior solutions"). The followers' efforts are chosen by the leader subject to (8) and (11), the page's tie-break. The sign condition $g_n\le 0$ (p. 14) and the row/column sums of $B$ (p. 8) are not imposed; the strictness of $c_n$ is dropped.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, p. 16, Proposition 5 and eq. (12); proof App. A.4, p. 26

import Mathlib
import Definitions.Def_CarbonDoubleCount_Leader_Setting

namespace CarbonDoubleCount.Leader

open Finset

theorem proposition_5
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (A p : ℝ) (hA : 0 < A) (hp : 0 ≤ p)
    (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (hVdiff : ∀ n, Differentiable ℝ (V n))
    (hfdiff : ∀ i, Differentiable ℝ (fun e => f e i))
    (hVconc : ∀ n, ConcaveOn ℝ (CarbonDoubleCount.Planner.firmBox A n) (V n))
    (hVanti : ∀ n, AntitoneOn (V n) (CarbonDoubleCount.Planner.firmBox A n))
    (hfconv : ∀ i, ConvexOn ℝ (CarbonDoubleCount.Planner.effortBox A) (fun e => f e i))
    (hfanti : ∀ i, AntitoneOn (fun e => f e i) (CarbonDoubleCount.Planner.effortBox A))
    (hfnonneg : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ i, 0 ≤ f e i)
    (B : ι → κ → ℝ) (hB01 : ∀ n i, B n i = 0 ∨ B n i = 1)
    (hB : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ n i, (B n i = 1 ↔ ∑ j, dEff (fun e => f e i) e n j < 0))
    (L : ι) (πbar : ι → ℝ)
    (gE : (n : ι) → (act n → ℝ) → ℝ) (eE : (n : ι) → act n → ℝ)
    (hopt : IsOptimalPE A V f p L πbar gE eE)
    (hint : ∀ n j, 0 < eE n j ∧ eE n j < A) :
    PFFeasible A V f L πbar (rule12 V f p B πbar eE) eE ∧
      pfObjective V f p L (rule12 V f p B πbar eE) eE = peObjective V f p L gE eE ∧
      ∀ (g : ι → (κ → ℝ) → ℝ) (e : (n : ι) → act n → ℝ),
        PFFeasible A V f L πbar g e → pfObjective V f p L g e ≤ peObjective V f p L gE eE := by sorry

end CarbonDoubleCount.Leader
