-- Prove2me | Theorems.Thm_DermanSeqDecisions_LinProg_total_cost_eq_cycle
-- name    : DermanSeqDecisions.LinProg.total_cost_eq_cycle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:45:16.878723+00:00
-- url     : https://prove2.me/theorems/12e861ba-8998-4c94-b533-8b615d6569f9
-- title:
--   (7): under Assumption B, the average total cost $\frac{1}{L+1}\sum_i S_R(i)$ is a cycle cost of the chain with the adjoined state $-1$
-- statement:
--   Consider Problem 2: stochastic chance laws $q_{ij}(k)$ on $\{0, \dots, L\}$, the state $L$ absorbing under every decision, $w_{Lk} = 0$, $w_{ik} > 0$ for $i \ne L$, and **Assumption B**: for every procedure of $C'$, the state $L$ is reached from every state with probability $1$. Adjoin the state $-1$, from which the chain moves to each of $0, \dots, L$ with probability $1/(L+1)$, and send $L$ to $-1$ with probability $1$; set $w_{-1,k} = 0$.
--
--   Let $D \in C'$, extended to $-1$ by any decision probabilities, let $\pi$ be a stationary distribution of the augmented chain, and put $f(j) = \sum_k D_{jk} w_{jk}$ (so $f(-1) = 0$). Then $\pi_{-1} > 0$, the taboo series converge, and
--   $$\frac{1}{L+1}\sum_{i=0}^{L} S_R(i) = \sum_{t=0}^{\infty}\sum_{j=-1}^{L} {}_{-1}p^{(t)}_{-1,j}\, f(j) = \frac{1}{\pi_{-1}}\sum_{j=-1}^{L} \pi_j f(j).$$
--
--   This turns the average of the total costs into a ratio of two linear functions of the state-action frequencies, which is the program (9).
--
--   **Formalization Note.** $L+1$ is the number of original states. Assumption B is stated as reachability of $L$ from every state ($\exists t,\ p^{(t)}_{iL} > 0$); for a finite chain in which $L$ is absorbing this is equivalent to absorption with probability $1$. The paper assumes $w_{ik} > 0$ (p. 17) and $w_{Lk} = 0$ in Problem 2; the consistent reading $w_{ik} > 0$ for $i \ne L$ is used. $S_R(i)$ takes values in $[0, \infty]$; the right-hand sides are nonnegative reals.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 21, §3, proof of Theorem 2, display (7)

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix

open scoped ENNReal

namespace DermanSeqDecisions.LinProg

/-- (7), p. 21 (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, proof of Theorem 2, display (7)).

Problem 2 under Assumption B: the chance laws are stochastic, `L` is absorbing under every decision,
`w_{Lk} = 0`, `w_{ik} > 0` for `i ≠ L`, and for every procedure of `C′` the state `L` is
reachable from every state. Adjoin the state `−1` (`none`) as on p. 21. For every `D ∈ C′`
(extended to `−1` by any decision probabilities `D₀`) and every stationary vector `π` of the
augmented chain `P`, with `f(j) = ∑_k D_{jk} w_{jk}` (`f(−1) = 0`):
`π_{−1} > 0`, the taboo probabilities `_{−1}p^{(t)}_{−1,j}` are summable in `t`, and
$$\frac{1}{L+1}\sum_{i=0}^{L} S_R(i) = \sum_{t=0}^{\infty}\sum_{j=-1}^{L} {}_{-1}p^{(t)}_{-1,j} f(j)
  = \frac{1}{\pi_{-1}}\sum_{j=-1}^{L}\pi_j f(j).$$

**Formalization Note.** `L + 1` is `Fintype.card S`. Assumption B ("`L` is accessible from
`0, ⋯, L − 1` within a finite number of transitions with probability 1") is stated as
reachability, `∀ i, ∃ t, 0 < (P_D^t)_{iL}`: for a finite chain in which `L` is absorbing,
reaching `L` with probability 1 from every state is equivalent to `L` being reachable from every
state. The paper states `w_{ik} > 0` on p. 17 and `w_{Lk} = 0` in Problem 2; the consistent reading
`w_{ik} > 0` for `i ≠ L` is used. `S_R(i)` is `totalCost` in `ℝ≥0∞`; the right-hand sides are
nonnegative reals. -/
theorem total_cost_eq_cycle {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act]
    (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (hwL : ∀ a, w L a = 0) (hw : ∀ i a, i ≠ L → 0 < w i a)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D)
    (D₀ : Act → ℝ) (hD₀ : (∀ a, 0 ≤ D₀ a) ∧ ∑ a, D₀ a = 1)
    (π : Option S → ℝ)
    (hπ : JewellMRP.InfiniteStep.IsStationary (chainMatrix (augLaw q L) (augProc D D₀)) π) :
    0 < π none ∧
    (∀ j, Summable (fun t : ℕ => tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j)) ∧
    (1 / (Fintype.card S : ℝ≥0∞)) * ∑ i, totalCost q w D i =
      ENNReal.ofReal (∑' t : ℕ, ∑ j, tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j *
        ∑ a, augProc D D₀ j a * augCost w j a) ∧
    ∑' t : ℕ, ∑ j, tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j *
        ∑ a, augProc D D₀ j a * augCost w j a =
      (1 / π none) * ∑ j, π j * ∑ a, augProc D D₀ j a * augCost w j a := by sorry

end DermanSeqDecisions.LinProg
