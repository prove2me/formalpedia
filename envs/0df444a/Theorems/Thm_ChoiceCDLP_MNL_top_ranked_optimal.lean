-- Prove2me | Theorems.Thm_ChoiceCDLP_MNL_top_ranked_optimal
-- name    : ChoiceCDLP.MNL.top_ranked_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T07:58:53.876838+00:00
-- url     : https://prove2.me/theorems/a54d53e6-63ca-4219-be6b-b613f62ee57c
-- title:
--   Proposition 6 — under MNL, offering every product with w_j ≥ w_[k*] is optimal for (14) (repaired: some w_j ≥ 0)
-- statement:
--   Consider one customer segment with a finite consideration set $\iota$, MNL preference weights $v_j > 0$ ($j \in \iota$), a no-purchase weight $v_0 \ge 0$ and scores $w_j \in \mathbb{R}$, at least one of which is nonnegative. For an offer set $S \subseteq \iota$ let
--   $$f(S) = \frac{\sum_{j \in S} w_j v_j}{\sum_{j \in S} v_j + v_0}.$$
--   Then there is a product $k \in \iota$ such that the threshold set $S^* = \{ j \in \iota : w_j \ge w_k \}$ is an optimal solution of the offer-set problem (14):
--   $$f(S) \le f\bigl(\{ j \in \iota : w_j \ge w_k\}\bigr) \qquad \text{for every } S \subseteq \iota.$$
--   In the paper's words: rank the scores decreasingly, $w_{[1]} \ge \cdots \ge w_{[s]}$; there is a critical value $k^*$, $1 \le k^* \le s$, such that offering exactly the products with $w_j \ge w_{[k^*]}$ is optimal. Here $w_k$ plays the role of $w_{[k^*]}$.
--
--   The result makes the column-generation subproblem of the choice-based deterministic linear program (CDLP), and the set-selection problems of the decomposition heuristic, solvable under MNL with disjoint segments by checking at most $s$ nested candidate sets, one per segment, instead of $2^s$ subsets. It was also shown by Gallego, Iyengar, Phillips and Dubey (2004).
--
--   **Formalization Note.** Offer vectors $y \in \{0,1\}^s$ are subsets `S : Finset ι`; the consideration set is the whole finite type `ι`. The ranking is not formalized as a permutation: the $k^*$-th largest value $w_{[k^*]}$ is the score $w_k$ of some product $k$, and $1 \le k^* \le s$ becomes "$k \in \iota$". With ties the threshold set contains every product tied with $w_{[k^*]}$, which is what the printed rule $y^*_j = 1 \iff w_j \ge w_{[k^*]}$ says. *Repair:* the hypothesis that some $w_j \ge 0$ is added. As printed the proposition is false when every $w_j < 0$: for $s = 1$, $w_1 = -1$, $v_1 = 1$, $v_0 = 1$, the empty offer set has value $0$ while the only set allowed by $1 \le k^*$, namely $\{1\}$, has value $-1/2$. Negative scores do occur in the paper's application ($w_j = r_j - \pi^\top A_j$, p. 300). The conclusion is that $S^*$ is *an* optimal solution; optimal solutions need not be unique. $v_0 = 0$ is allowed (the paper uses it in §7), with $f(\emptyset) = 0/0 = 0$ in Lean, the paper's convention $h(0) := 0$.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 300, Proposition 6

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

namespace ChoiceCDLP.MNL

/-- Proposition 6 (Liu and van Ryzin 2008, p. 300). For one segment with consideration set `ι`
(finite), preference weights `v j > 0`, no-purchase weight `v₀ ≥ 0` and scores `w j`, there is
a product `k` (the `k*`-th ranked, `w k = w_[k*]`) such that offering every product with
`w j ≥ w k` is an optimal solution of
`max_{S ⊆ ι} (∑_{j ∈ S} w_j v_j) / (∑_{j ∈ S} v_j + v₀)` (problem (14)).
Repaired: the hypothesis that some `w j ≥ 0` is added (as printed, `1 ≤ k*` is false when
every `w j < 0`, where only the empty offer set is optimal). -/
theorem top_ranked_optimal {ι : Type*} [Fintype ι] (v w : ι → ℝ) (v₀ : ℝ)
    (hv : ∀ j, 0 < v j) (hv₀ : 0 ≤ v₀) (hw : ∃ j, 0 ≤ w j) :
    ∃ k : ι, ∀ S : Finset ι,
      mnlObjective v w v₀ S ≤ mnlObjective v w v₀ (Finset.univ.filter fun j => w k ≤ w j) := by sorry

end ChoiceCDLP.MNL
