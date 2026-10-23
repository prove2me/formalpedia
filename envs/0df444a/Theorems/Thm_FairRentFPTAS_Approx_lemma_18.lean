-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_lemma_18
-- name    : FairRentFPTAS.Approx.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:31.793817+00:00
-- url     : https://prove2.me/theorems/ab534d44-8c81-4d2e-b187-93e4bc92f38e
-- title:
--   Lemma 18, p. 38 — a nonnegative weight matrix with a positive matching admits multiplicatively envy-free scalings
-- statement:
--   Let $W=(W_{(a,r)})_{a,r\in[n]}$ have nonnegative entries and suppose some perfect matching $\pi$ has $W_{(a,\pi(a))}>0$ for all $a$. Then there are a perfect matching $\sigma$ and a vector $d\in\mathbb R^n$ with $d_r>0$ for all $r$ such that
--   $$d_{\sigma(a)}W_{(a,\sigma(a))}\ \ge\ d_rW_{(a,r)}\qquad\text{for all }a,r\in[n].$$
--
--   It is the multiplicative counterpart of Lemma 16 and the key step of the proof of the perturbation Lemma 2.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 38, Appendix B, Lemma 18

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Lemma 18, p. 38: if a nonnegative weight matrix `W` admits a perfect matching of
positive weights, then some matching `σ` and some positive vector `d` satisfy
`d_{σ(a)} W_{(a,σ(a))} ≥ d_r W_{(a,r)}` for all `a, r`. -/
theorem lemma_18 {n : ℕ} (W : Fin n → Fin n → ℝ) (hW : ∀ a r, 0 ≤ W a r)
    (hpos : ∃ π : Equiv.Perm (Fin n), ∀ a, 0 < W a (π a)) :
    ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℝ), (∀ r, 0 < d r) ∧
      ∀ a r, d r * W a r ≤ d (σ a) * W a (σ a) := by sorry

end FairRentFPTAS.Approx
