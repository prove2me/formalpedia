-- Prove2me | Theorems.Thm_Arxiv2412_03183_gain_constraint_prevents_zero
-- name    : Arxiv2412_03183.gain_constraint_prevents_zero
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T13:51:52.211624+00:00
-- url     : https://prove2.me/theorems/cff66fb9-b0ca-4892-a81e-c9aaf71347af
-- title:
--   Eq. (12): the gain constraint prevents the gains from shrinking to $0$
-- statement:
--   Let $g$ satisfy the constraint of eq. (12), $\sum_l|g_{\alpha l}|=N_\alpha$ for every station $\alpha$. Then for every station $\alpha$ with $N_\alpha\ge1$ some gain of $\alpha$ has modulus at least $1$, $\max_l|g_{\alpha l}|\ge1$. In particular the gains of a station cannot all be $0$, or all tend to $0$.
--
--   **Formalization Note** The paper's sentence "the constraint prevents the gain from shrinking to $0$" is read station by station: the gains of a station cannot all shrink to $0$. Individual gains can be $0$, as the paper itself notes.
-- source:
--   Ikeda, Nakazato, Tsukagoshi, Takeuchi and Yamaguchi, Solving Self-calibration of ALMA Data with an Optimization Method, arXiv:2412.03183v1 (2024), claim c003; Section 3.2, constraint of eq. (12), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2412_03183_Basic

open Finset

namespace Arxiv2412_03183

theorem gain_constraint_prevents_zero {S : Type*} {N : S → ℕ} (g : Gains N)
    (hg : g ∈ gainFeasible N) (α : S) (hα : 0 < N α) :
    ∃ i : Fin (N α), 1 ≤ ‖g ⟨α, i⟩‖ := by sorry

end Arxiv2412_03183
