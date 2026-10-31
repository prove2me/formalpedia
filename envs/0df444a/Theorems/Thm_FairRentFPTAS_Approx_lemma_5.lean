-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_lemma_5
-- name    : FairRentFPTAS.Approx.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:35.309843+00:00
-- url     : https://prove2.me/theorems/bab23b7f-cd49-4372-9ca9-3ac8bd9bee06
-- title:
--   Lemma 5, p. 12 — the rents of Algorithm 1 never increase
-- statement:
--   Let $J$ be a well-formed instance, $M$ a threshold and $(\pi^k,p^k)_{0\le k\le T}$ a run of Algorithm 1. For every $1\le i\le T$ the price vectors of consecutive iterations satisfy, componentwise,
--   $$p^{i-1}\ \ge\ p^i.$$
--
--   Monotonicity of the rents is what makes each linear-domain boundary crossable only once, which bounds the number of domain changes.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 12, Lemma 5

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Lemma 5, p. 12: the prices computed in consecutive iterations of Algorithm 1 satisfy
`p^{i−1} ≥ pⁱ` componentwise. -/
theorem lemma_5 {n : ℕ} (J : Instance n) (M : ℝ) (hJ : Standing J) (hM : IsThreshold J M)
    (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ) (hrun : IsRun J M T π p)
    (i : ℕ) (hi : 1 ≤ i) (hiT : i ≤ T) :
    ∀ r, p i r ≤ p (i - 1) r := by sorry

end FairRentFPTAS.Approx
