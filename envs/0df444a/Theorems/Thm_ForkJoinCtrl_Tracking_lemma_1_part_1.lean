-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_lemma_1_part_1
-- name    : ForkJoinCtrl.Tracking.lemma_1_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:42.679343+00:00
-- url     : https://prove2.me/theorems/04a08834-9bc2-4840-9bae-b335de17da82
-- title:
--   Lemma 1 Part 1, p. 12 — an optimal solution of LP (18) solves the convex problem (17), with equal optimal values
-- statement:
--   Let $b\in\mathbb R^{a_2}_+$ and let $(\tilde y,\tilde q)$ be an optimal solution of the LP (18) at $b$ (feasible, with the least objective value among feasible points). Then $\tilde q$ is feasible and optimal for the convex problem (17),
--
--   $$\sum_{j}h_j\Big(\max_{k\in\mathcal K_j}q_k\vee\max_{i\in\mathcal I_j}\tilde q_{ij}\Big)=\min_{q\ \text{feasible for (17)}}\ \sum_j h_j\Big(\max_{k\in\mathcal K_j}q_k\vee\max_{i\in\mathcal I_j}q_{ij}\Big),$$
--
--   and the optimal values of (17) and (18) coincide: the left-hand side equals $\sum_j h_j\tilde y_j$.
--
--   The lemma lets the nonsmooth cost $\sum_j h_j N_j$ be evaluated by a linear program, so that the asymptotic lower bound is $z$.
--
--   **Formalization Note** The holding costs $h_j\ge0$ and rates $\mu_{ij}>0$ are those of the network.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 12, Lemma 1 Part 1

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_LP

namespace ForkJoinCtrl.Tracking

theorem lemma_1_part_1 (N : Network) (b : LPParam N) (hb : b.Nonneg) (x : LPVar N)
    (hxf : LPFeasible N b x)
    (hxopt : IsLeast (LPObj N '' {x' | LPFeasible N b x'}) (LPObj N x)) :
    Feas17 N b x.q ∧ IsLeast (Obj17 N b '' {q | Feas17 N b q}) (Obj17 N b x.q) ∧
      Obj17 N b x.q = LPObj N x := by sorry

end ForkJoinCtrl.Tracking
