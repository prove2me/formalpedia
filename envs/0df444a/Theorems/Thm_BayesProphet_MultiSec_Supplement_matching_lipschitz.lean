-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_Supplement_matching_lipschitz
-- name    : BayesProphet.MultiSec.Supplement.matching_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:10:15.715262+00:00
-- url     : https://prove2.me/theorems/16916007-4d68-464a-8bc4-56e7458f1b83
-- title:
--   Proposition 4 (corrected: demand vectors in ℝⁿ) — Lipschitz property for matching with constant 1
-- statement:
--   Consider the matching LP of Eq. (13) with $d$ resources, $n$ types, adjacency matrix $A\in\{0,1\}^{d\times n}$ and rewards $r\in\mathbb R^{d\times n}_{\ge0}$:
--   $$P[z,b]:\quad\max\sum_{i,j}x_{ij}r_{ij}a_{ij}\ \text{ s.t. }\ \sum_j x_{ij}\le b_i\ (i\in[d]),\ \ \sum_{i}x_{ij}\le z_j\ (j\in[n]),\ \ x\ge0.$$
--   Take any $z^1,z^2\in\mathbb R^n_{\ge0}$ and $b\in\mathbb R^d_{\ge0}$. If $x^1$ is an optimal solution of $P[z^1,b]$, then there exists an optimal solution $x^2$ of $P[z^2,b]$ such that
--   $$\|x^1-x^2\|_\infty\ \le\ \|z^1-z^2\|_1 .$$
--
--   The Lipschitz constant is exactly $1$, independently of $d$, $n$, the adjacency matrix and the rewards. In the analysis of Theorem 4 it bounds how far Offline's ex-post solution can be from the fluid solution in terms of the deviation of the arrival counts.
--
--   **Formalization Note** $\|x\|_\infty=\max_{i,j}|x_{ij}|$ is Lean's sup norm on `Fin d → Fin n → ℝ`. The statement is "for every optimizer $x^1$ there is a nearby optimizer $x^2$", not a claim about any pair of optimizers.
--
--   Differences from the source:
--   - correction: the source writes $z^1,z^2\in\mathbb R^d_{\ge0}$ → Lean: $z^1,z^2\in\mathbb R^n_{\ge0}$; reason: in Eq. (13) $z$ is the right-hand side of the $n$ type constraints $\sum_i x_{ij}\le z_j$, and the proof in Appendix B.5 writes $Dx\le z$ with $D\in\mathbb R^{n\times nd}$; $\mathbb R^d$ is a dimension typo.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 25, Proposition 4 (LP Eq. (13), p. 23; proof Appendix B.5, pp. 38–39)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_Supplement_Matching

namespace BayesProphet.MultiSec.Supplement

theorem matching_lipschitz {d n : ℕ} (adj : Fin d → Fin n → Bool) (r : Fin d → Fin n → ℝ)
    (hr : ∀ i j, 0 ≤ r i j) (z₁ z₂ : Fin n → ℝ) (hz₁ : ∀ j, 0 ≤ z₁ j) (hz₂ : ∀ j, 0 ≤ z₂ j)
    (b : Fin d → ℝ) (hb : ∀ i, 0 ≤ b i) (x₁ : Fin d → Fin n → ℝ)
    (hx₁ : x₁ ∈ matchOpt adj r z₁ b) :
    ∃ x₂ ∈ matchOpt adj r z₂ b, ‖x₁ - x₂‖ ≤ ∑ j, |z₁ j - z₂ j| := by sorry

end BayesProphet.MultiSec.Supplement
