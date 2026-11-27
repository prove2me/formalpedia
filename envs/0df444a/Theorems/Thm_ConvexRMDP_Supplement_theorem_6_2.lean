-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_theorem_6_2
-- name    : ConvexRMDP.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:01:17.154807+00:00
-- url     : https://prove2.me/theorems/c7e6e1a5-4158-5e1e-ac8c-6305418cc93f
-- title:
--   Theorem 6.2 (corrected: min over $s'$ inside each action term; Slater point feasible) — (6.3) and the conic program (6.4) have the same optimal solutions
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an s-rectangular robust MDP with nonempty $\mathcal A$, satisfying Assumption 6.1 (with the corrected Slater condition) for convex constraint functions $g_{s,i} : \mathbb R^{\mathcal S \times \mathcal A} \to \mathbb R$, $i = 1, \dots, m$, and let $b > 0$. Then the set of optimal solutions to the convex program (6.3), $\max\{\sum_s x_s \mid 1 \le x_s \le \tilde t(x)_s,\ \forall s\}$ with $\tilde t$ of (6.2), coincides with the set of optimal solutions to the convex program (6.4), which maximizes $\sum_s x_s$ over $x \in \mathbb R^{\mathcal S}$ and auxiliary variables $\xi_s \in \mathbb R^m_+$, $y_s, y^i_s \in \mathbb R^{\mathcal A \times \mathcal S}$, $\alpha_{sa} \in \mathbb R_+$, $u_{sa}, w_{sa} \in \mathbb R$, $z_{sa} \in \mathbb R^{\mathcal S}$ subject to
--
--   $$
--   \begin{aligned}
--   & w_{sa} \le y_{sas'} + \omega_b(s,a)\, z_{sas'}, && \forall (s,a,s'),\\
--   & x_s \le -\sum_{i=1}^m \xi_{si}\, g^*_{s,i}\big(y^i_s/\xi_{si}\big) + \sum_{a \in \mathcal A}\Big( w_{sa} + \omega_b(s,a)\big(\tfrac{1-\gamma}{\gamma} u_{sa} + \tfrac{1+\log\gamma}{\gamma}\alpha_{sa}\big)\Big), && \forall s,\\
--   & (x_{s'}, \alpha_{sa}, z_{sas'}) \in \mathcal K_{\exp},\ (1, \alpha_{sa}, u_{sa}) \in \mathcal K_{\exp}, && \forall (s,a,s'),\\
--   & \textstyle\sum_{i=1}^m y^i_s = y_s,\quad x_s \ge 1 .
--   \end{aligned}
--   $$
--
--   Moreover (6.4) is a convex program: its feasible set is convex and closed.
--
--   **Formalization Note** "The optimal solutions coincide" means: the $x$-components of the optimal solutions of (6.4) are exactly the optimal solutions of (6.3). "Convex program" follows the paper's definition (§1.1, p.4). Perspective terms may be $+\infty$, making the right-hand side $-\infty$.
--
--   Differences from the source:
--   - correction: the constraint "$x_s \le -\sum_i \xi_{si} g^*_{s,i}(y^i_s/\xi_{si}) + \sum_a y_{sas'} + \omega_b(s,a)(z_{sas'} + \dots)$, $\forall s, s'$" (minimum over $s'$ outside the sum over actions) → `feasible64` with $w_{sa} \le y_{sas'} + \omega_b(s,a) z_{sas'}$ for all $s'$ (minimum inside each action term, as in Lemma 6.1); reason: as printed the theorem is false. With $\mathcal S = \mathcal A = \{1,2\}$ and $\mathcal U_s = \{P : P_1 = \delta_1, P_2 = \delta_2\}$ described by the affine constraints $1 - P_{11} \le 0$, $1 - P_{22} \le 0$, the printed (6.4) is unbounded ($\xi_s \to \infty$) while (6.3) has an optimal solution; with the Slater-satisfying $\mathcal U_s = \{P : P_{11} \ge 1/2, P_{22} \ge 1/2\}$ the printed right-hand side is $(\omega_b(s,1) + \omega_b(s,2))(x_1x_2)^{\gamma/2} > \tilde t(x)_s$ whenever $x_1 < x_2$.
--   - correction: Slater's condition of Assumption 6.1 → `Assumption61` (affine constraints at the Slater point); reason: the inner dual maxima of Lemma 6.1 must be attained for the optimum of (6.3) to be feasible for (6.4) (Boyd–Vandenberghe §5.2.3).
--   - reading: "$\mathcal U_{sa}$ … $g_s(p) \le 0, \forall i$" in Assumption 6.1 → $\mathcal U_s$ and $g_{s,i}(P) \le 0$ for all $i$; reason: the model is s-rectangular.
--   - encoding: "proper closed convex $g_{s,i}$ into $\mathbb R$" → `ConvexOn ℝ univ`; reason: automatic properness and continuity.
--   - encoding: "the set of optimal solutions coincides" and "convex program" → `Prod.fst` image of the optimal set of `feasible64` equals the optimal set of (6.3); `feasible64` is `Convex` and `IsClosed`; reason: the paper's notions (§1.1, p.4).
--   - encoding: nonempty $\mathcal A$ and $b>0$ → `[Nonempty A]` and `0 < b`; reason: standing assumptions required by the uniform weights and by $\log_b$; no source instance is excluded.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Theorem 6.2, program (6.4), p.21; built from (6.3), p.20, Lemma 6.1 and Lemma 5.1

import Mathlib
import Definitions.Def_ConvexRMDP_Supplement_Assumption61
import Definitions.Def_ConvexRMDP_Supplement_feasible64

namespace ConvexRMDP

namespace Supplement

/-- **Theorem 6.2 (corrected: min over s′ inside each action term; Slater point feasible)**
(Grand-Clément & Petrik, arXiv:2209.10187v2, p.21). Under Assumption 6.1, the set of optimal solutions
to the convex program (6.3), `max {∑_s x_s | 1 ≤ x_s ≤ t̃(x)_s, ∀ s}` with `t̃` of (6.2), coincides with
the set of optimal solutions to the convex program (6.4).

**Formalization Note.** (6.4) is `feasible64` with objective `∑_s x_s`, stated with the minimum over
`s'` inside each action term through the epigraph variable `w_{sa}` (the printed program puts it
outside the sum over actions; see `feasible64`), and Assumption 6.1 is `Assumption61` with the
corrected Slater condition. "The optimal solutions coincide" is: the `x`-components of the optimal
solutions of (6.4) are exactly the optimal solutions of (6.3). "Convex program" (§1.1, p.4: a concave
objective maximized over a closed convex set) is the last two clauses: the feasible set of (6.4), in all
its variables, is convex ("The concavity of (6.4) can be proved exactly as the concavity of (5.10)",
p.21) and closed (the objective is linear). `A` is nonempty and `b > 0`, as required by the uniform
weights. -/
theorem theorem_6_2 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : SRMDP S A) (b : ℝ) (hb : 0 < b) (m : ℕ) (g : S → Fin m → (A → S → ℝ) → ℝ)
    (hg : Assumption61 M m g) :
    Prod.fst '' {v | v ∈ feasible64 M b m g ∧
        ∀ v' ∈ feasible64 M b m g, ∑ s, v'.1 s ≤ ∑ s, v.1 s} =
      {x : S → ℝ | (∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s) ∧
        ∀ x' : S → ℝ, (∀ s, 1 ≤ x' s ∧ x' s ≤ M.tOp b x' s) → ∑ s, x' s ≤ ∑ s, x s} ∧
    Convex ℝ (feasible64 M b m g) ∧ IsClosed (feasible64 M b m g) := by sorry

end Supplement

end ConvexRMDP
