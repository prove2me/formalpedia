-- Prove2me | Theorems.Thm_ABPOnline_lemma_C_4
-- name    : ABPOnline.lemma_C_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:53:42.74719+00:00
-- url     : https://prove2.me/theorems/79308971-7cdd-4eb9-ae51-e1b45edf827e
-- title:
--   Lemma C.4 — accumulated contraction error $\max_n|e_n|\le2\max_n|P_n|$
-- statement:
--   Let $e_0=P_0=0$ and suppose
--   $$
--   e_{n+1}=\theta_ne_n+(P_{n+1}-P_n),\qquad 0\le\theta_n\le1 .
--   $$
--   Then
--   $$
--   \max_{0\le n\le L}|e_n|\le2\max_{0\le n\le L}|P_n| .
--   $$
--
--   This accumulates the local discretization errors of the Euler scheme in Lemma 4.5.
--
--   Differences from the source:
--   - encoding: the recursion and 0 ≤ θ_n ≤ 1 for the relevant n → assumed for n < L; reason: exactly the indices that determine e_0, …, e_L
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Lemma C.4, p.40 (PDF p.41)

import Mathlib

set_option autoImplicit false

namespace ABPOnline

/-- **Lemma C.4** (arXiv:2609.02124, printed p.40, PDF p.41). Let `e_0 = P_0 = 0` and suppose
`e_{n+1} = θ_n e_n + (P_{n+1} − P_n)` with `0 ≤ θ_n ≤ 1`. Then
`max_{0≤n≤L} |e_n| ≤ 2 max_{0≤n≤L} |P_n|`.

**Formalization Note** The recursion and the bounds on `θ_n` are assumed for `n < L`, the indices
that reach `e_0, …, e_L`. -/
theorem lemma_C_4 (L : ℕ) (e Pseq θ : ℕ → ℝ) (he0 : e 0 = 0) (hP0 : Pseq 0 = 0)
    (hrec : ∀ n < L, e (n + 1) = θ n * e n + (Pseq (n + 1) - Pseq n))
    (hθ : ∀ n < L, 0 ≤ θ n ∧ θ n ≤ 1) :
    (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one (fun n => |e n|) ≤
      2 * (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one (fun n => |Pseq n|) := by sorry

end ABPOnline
