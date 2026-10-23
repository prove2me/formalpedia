-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_lemma_4
-- name    : FairRentFPTAS.Approx.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:31.322908+00:00
-- url     : https://prove2.me/theorems/6f2ae0e1-f8f6-4115-9a59-2959ee1555cd
-- title:
--   Lemma 4, p. 12 — inside one linear domain the matching weight strictly increases
-- statement:
--   Let $J$ be a well-formed instance with $n\ge1$ agents, $M$ a threshold, and $(\pi^k,p^k)_{0\le k\le T}$ a run of Algorithm 1. If $1\le i$, iteration $i+1$ is executed ($i+1\le T$), and the linear domain does not change in iteration $i$, $(L^{i-1},U^{i-1})=(L^i,U^i)$, then, with weights taken in $\mathcal F^w(p^i)$,
--   $$w(\pi^i)<w(\pi^{i+1}).$$
--
--   This strict increase, together with the integrality of the weights under the powers-of-$(1+\varepsilon)$ property, bounds the number of iterations spent in one linear domain.
--
--   **Formalization Note** The page takes the existence of $\pi^{i+1}$ for granted; the hypothesis $i+1\le T$ states it. The hypothesis $n\ge1$ excludes the empty instance, on which the guard never fails and all weights are $0$.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 12, Lemma 4

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Lemma 4, p. 12: if the linear domain does not change in iteration `i`,
`(L^{i−1}, U^{i−1}) = (Lⁱ, Uⁱ)`, and iteration `i + 1` is executed, then
`w(πⁱ) < w(π^{i+1})` in `F_w(pⁱ)`. -/
theorem lemma_4 {n : ℕ} (hn : 1 ≤ n) (J : Instance n) (M : ℝ) (hJ : Standing J)
    (hM : IsThreshold J M) (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ)
    (hrun : IsRun J M T π p) (i : ℕ) (hi : 1 ≤ i) (hiT : i + 1 ≤ T)
    (hdom : domL (hatInst M J) (p (i - 1)) = domL (hatInst M J) (p i) ∧
      domU (hatInst M J) (p (i - 1)) = domU (hatInst M J) (p i)) :
    weight (hatInst M J) (p i) (π i) < weight (hatInst M J) (p i) (π (i + 1)) := by sorry

end FairRentFPTAS.Approx
