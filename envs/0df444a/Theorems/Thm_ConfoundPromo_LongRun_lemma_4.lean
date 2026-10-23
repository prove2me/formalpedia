-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_lemma_4
-- name    : ConfoundPromo.LongRun.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:25.329954+00:00
-- url     : https://prove2.me/theorems/d5686cd8-0212-4586-b115-9bfda1827073
-- title:
--   Lemma 4, p. OA–15 — co(W^max) − co(W^C) is bounded by ε/2 + C̄µ and by ε/2 + C̄(1 − µ)
-- statement:
--   Fix a market satisfying the standing assumptions and $\epsilon>0$. There is $\bar C\ge0$ such that for all $\mu\in[0,1]$,
--   $$
--   co(W^{\max})(\mu)-co(W^C)(\mu)<\frac{\epsilon}{2}+\bar C\mu,\qquad co(W^{\max})(\mu)-co(W^C)(\mu)<\frac{\epsilon}{2}+\bar C(1-\mu).
--   $$
--   Here $W^{\max}(\mu)$ is the largest one-period surplus any promotion rule can generate at belief $\mu$, and $W^C(\mu)$ the largest one-period surplus of a confounding rule.
--
--   Near a degenerate belief the gain from not confounding vanishes linearly, which is what makes exponential learning (Lemma 3) sufficient in the proof of Theorem 1.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. OA–15 (PDF 49), Lemma 4

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- Lemma 4 (p. OA–15): co(W^max) − co(W^C) is bounded by ε/2 + C̄μ and by ε/2 + C̄(1 − μ). -/
theorem lemma_4 (M : Market) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cbar : ℝ, 0 ≤ Cbar ∧ ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      co (Wmax M) μ - co (WC M) μ < ε / 2 + Cbar * μ ∧
      co (Wmax M) μ - co (WC M) μ < ε / 2 + Cbar * (1 - μ) := by sorry

end ConfoundPromo.LongRun
