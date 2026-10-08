-- Prove2me | Theorems.Thm_AffinePolicies_TwoGap_lemma_3
-- name    : AffinePolicies.TwoGap.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:39:05.646016+00:00
-- url     : https://prove2.me/theorems/a59e4e3b-4d6b-4afe-81a6-8bfbbdcc635c
-- title:
--   Lemma 3, PDF p. 11 — on ℐ there is an optimal affine solution ŷ(b) = P̂b + q̂ with all q̂_i equal
-- statement:
--   Let $m \ge 1$ be even and consider the instance $\mathcal I$ of (6). Then there exist a first-stage decision $x \in \mathbb R^m$, a matrix $\hat P \in \mathbb R^{m\times m}$ and a vector $\hat q \in \mathbb R^m$ such that $x$ together with the affine policy
--   $$\hat y(b)=\hat P b+\hat q$$
--   is an **optimal affine solution** of $\Pi_{\mathrm{Adapt}}(\mathcal U)$ (feasible, and with worst-case cost no larger than that of any feasible affine solution), and
--   $$\hat q_i=\hat q_j\qquad\text{for all } i,j\in\{1,\dots,m\}.$$
--
--   The lemma lets the proof of Theorem 2 work with a single scalar $\beta = \hat q_j$ for the constant part of the policy.
--
--   **Formalization Note** The lemma asserts that the minimum defining $z_{\mathrm{Aff}}$ is attained, by a solution with constant intercept. Optimality is stated directly: the solution is feasible, and its worst-case cost is bounded by every bound achieved by any feasible affine solution. The first-stage vector $x$ is part of the solution (it plays no role here since $A = 0$ and $c = 0$). The hypothesis $m > 0$ excludes the empty instance.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 3, PDF p. 11

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

namespace AffinePolicies.TwoGap

theorem lemma_3 (m : ℕ) (hm_even : Even m) (hm0 : 0 < m) :
    ∃ (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ),
      AffinePolicies.Simplex.IsOptimalAff (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) x P q ∧ ∀ i j, q i = q j := by sorry

end AffinePolicies.TwoGap
