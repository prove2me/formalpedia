-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_theorem_5_1
-- name    : ConvexRMDP.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:59:17.257256+00:00
-- url     : https://prove2.me/theorems/2ae5eb9e-37ff-49c3-98c0-36c3e0727360
-- title:
--   Theorem 5.1 (corrected: min over $s'$ inside each action term; Slater point feasible, in relint dom) — (4.7) and the conic program (5.10) have the same optimal solutions
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP with nonempty $\mathcal A$, satisfying Assumption 5.1 (with the corrected Slater condition) for constraint functions $g_{sa,i}$, $i = 1, \dots, m$, and let $b > 0$. Then the set of optimal solutions to the convex program
--
--   $$
--   \max\Big\{\sum_{s \in \mathcal S} x_s \;\Big|\; 1 \le x_s \le \tilde t(x)_s,\ \forall s \in \mathcal S\Big\} \tag{4.7}
--   $$
--
--   coincides with the set of optimal solutions to the convex program (5.10), which maximizes $\sum_s x_s$ over $x \in \mathbb R^{\mathcal S}$ and auxiliary variables $\xi_{sa} \in \mathbb R^m_+$, $\alpha_{sa} \in \mathbb R_+$, $y_{sa}, y^i_{sa}, z_{sa} \in \mathbb R^{\mathcal S}$, $u_{sa}, w_{sa} \in \mathbb R$ subject to
--
--   $$
--   \begin{aligned}
--   & w_{sa} \le y_{sas'} + z_{sas'}, && \forall (s,a,s'),\\
--   & x_s \le \sum_{a \in \mathcal A} \omega_b(s,a)\Big( w_{sa} + \tfrac{1-\gamma}{\gamma} u_{sa} + \tfrac{1+\log\gamma}{\gamma}\alpha_{sa} - \sum_{i=1}^m \xi_{sai}\, g^*_{sa,i}\big(y^i_{sa}/\xi_{sai}\big)\Big), && \forall s,\\
--   & (x_{s'}, \alpha_{sa}, z_{sas'}) \in \mathcal K_{\exp},\ (1, \alpha_{sa}, u_{sa}) \in \mathcal K_{\exp}, && \forall (s,a,s'),\\
--   & \textstyle\sum_{i=1}^m y^i_{sa} = y_{sa},\quad x_s \ge 1 .
--   \end{aligned}
--   $$
--
--   Moreover (5.10) is a convex program: its feasible set is convex and closed.
--
--   The theorem removes the inner minimization over the uncertainty sets from (4.7): the robust problem becomes a single exponential-cone program.
--
--   **Formalization Note** "The optimal solutions coincide" means: the $x$-components of the optimal solutions of (5.10) are exactly the optimal solutions of (4.7). "Convex program" follows the paper's definition (§1.1, p.4): a concave objective maximized over a closed convex set; the objective is linear, so the claim is that the feasible set of (5.10), in all its variables, is convex and closed. The perspective terms may equal $+\infty$; the right-hand side of the $x_s$ constraint is then $-\infty$.
--
--   Differences from the source:
--   - correction: the constraint "$x_s \le \sum_a \omega_b(s,a)\big(y_{sas'} + z_{sas'} + \dots\big)$, $\forall s, s'$" (minimum over $s'$ outside the sum over actions) → `feasible510` with $w_{sa} \le y_{sas'} + z_{sas'}$ for all $s'$ and $w_{sa}$ in place of $y_{sas'} + z_{sas'}$ (minimum inside each action term, as in (5.3)); reason: as printed the theorem is false. With $\mathcal S = \mathcal A = \{1,2\}$, $\mathcal U_{s1} = \{\delta_1\}$, $\mathcal U_{s2} = \{\delta_2\}$ described by the affine constraints $1 - p_1 \le 0$ and $1 - p_2 \le 0$, letting $\xi_{sa} \to \infty$ makes every right-hand side tend to $+\infty$, so the printed (5.10) is unbounded while (4.7) has an optimal solution. With the Slater-satisfying sets $\mathcal U_{s1} = \{p : p_1 \ge 1/2\}$, $\mathcal U_{s2} = \{p : p_2 \ge 1/2\}$ the printed right-hand side exceeds $\tilde t(x)_s$ whenever $x_1 \ne x_2$, and with $r_{1a} \neq r_{2a}$ the optimum of (4.7) is not optimal for the printed program.
--   - correction: Slater's condition of Assumption 5.1 → `Assumption51` (Slater point also in $\operatorname{relint}\operatorname{dom}(g_{sa,i})$ and satisfying the affine constraints); reason: with the printed condition the inner dual maxima need not be attained (counterexample under Proposition 5.1), and then the optimum of (4.7) is not feasible for (5.10), which has no optimal solution.
--   - encoding: "the set of optimal solutions coincides" and "convex program" → the image under `Prod.fst` of the optimal set of (5.10) equals the optimal set of (4.7); the feasible set of (5.10) is `Convex` and `IsClosed`; reason: the paper's notions (convex program, §1.1 p.4).
--   - encoding: nonempty $\mathcal A$ and $b>0$ → `[Nonempty A]` and `0 < b`; reason: standing assumptions required by the uniform weight $\omega_b(s,a)=\exp(b r_{sa})/|\mathcal A|$ and by $\log_b$; no source instance is excluded.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Theorem 5.1, program (5.10), p.18; built from (5.1), p.15, and Proposition 5.1, p.16

import Mathlib
import Definitions.Def_ConvexRMDP_Supplement_Assumption51
import Definitions.Def_ConvexRMDP_Supplement_feasible510

namespace ConvexRMDP

namespace Supplement

/-- **Theorem 5.1 (corrected: min over s′ inside each action term; Slater point feasible, in relint
dom)** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.18). Under Assumption 5.1, the set of optimal
solutions to the convex program (4.7), `max {∑_s x_s | 1 ≤ x_s ≤ t̃(x)_s, ∀ s}`, coincides with the set
of optimal solutions to the convex program (5.10).

**Formalization Note.** (5.10) is `feasible510` with objective `∑_s x_s`, stated with the
minimum over `s'` inside each action term through the epigraph variable `w_{sa}` (the printed program
puts it outside the sum over actions and is unbounded on simple instances; see `feasible510`), and
Assumption 5.1 is `Assumption51` with the corrected Slater condition. "The optimal solutions coincide"
is: the `x`-components of the optimal solutions of (5.10) are exactly the optimal solutions of (4.7).
"Convex program" (§1.1, p.4: a concave objective maximized over a closed convex set) is the last two
clauses: the feasible set of (5.10), in all its variables, is convex (the convexity of the constraints,
which is the proof printed on p.18) and closed (the objective is linear). `A` is nonempty and
`b > 0`, as required by the uniform weights. -/
theorem theorem_5_1 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) (m : ℕ) (g : S → A → Fin m → (S → ℝ) → EReal)
    (hg : Assumption51 M m g) :
    Prod.fst '' {v | v ∈ feasible510 M b m g ∧
        ∀ v' ∈ feasible510 M b m g, ∑ s, v'.1 s ≤ ∑ s, v.1 s} =
      {x : S → ℝ | (∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s) ∧
        ∀ x' : S → ℝ, (∀ s, 1 ≤ x' s ∧ x' s ≤ M.tOp b x' s) → ∑ s, x' s ≤ ∑ s, x s} ∧
    Convex ℝ (feasible510 M b m g) ∧ IsClosed (feasible510 M b m g) := by sorry

end Supplement

end ConvexRMDP
