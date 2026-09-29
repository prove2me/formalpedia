-- Prove2me | Theorems.Thm_DrezetGHZ_ghz_nonsignaling
-- name    : DrezetGHZ.ghz_nonsignaling
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T21:01:25.26064+00:00
-- url     : https://prove2.me/theorems/881c1fc1-89e7-4de0-a0e7-14f1cbbd22df
-- title:
--   Eq. (29): quantum non-signalling for the GHZ state
-- statement:
--   For the GHZ state $|\psi\rangle$ and settings in $\{\hat x,\hat y\}$:
--
--   1. **Non-signalling (Eq. (29)).** Alice's marginal does not depend on Bob's and Charlie's settings: for all $\hat n_1,\hat n_2,\hat n_3,\hat n_2',\hat n_3'$ and $\alpha\in\{\pm1\}$,
--   $$\sum_{\beta,\gamma}P(\alpha,\beta,\gamma\mid\hat n_1,\hat n_2,\hat n_3,\psi)=\sum_{\beta,\gamma}P(\alpha,\beta,\gamma\mid\hat n_1,\hat n_2',\hat n_3',\psi).$$
--   2. **Alice's $\hat x$-marginal is uniform:** for all $\hat n_2,\hat n_3$ and $\alpha$,
--   $$P_1(\alpha\mid\hat x,\psi)=\sum_{\beta,\gamma}P(\alpha,\beta,\gamma\mid\hat x,\hat n_2,\hat n_3,\psi)=\tfrac12.$$
--
--   The paper cites this as the non-signalling property that advocates of Everettian locality appeal to, and which it distinguishes from Bell's local causality.
-- source:
--   A. Drezet, "An Elementary Proof That Everett's Quantum Multiverse Is Nonlocal: Bell-Locality and Branch-Symmetry in the Many-Worlds Interpretation", arXiv:2306.07794v1 [quant-ph] (2023), https://arxiv.org/abs/2306.07794, p. 10, Eq. (29); p. 11: "there are only two worlds $|A_{+1_x}\rangle$, $|A_{-1_x}\rangle$ with the same probability $P_1(\pm1\mid\hat x,\psi)=1/2$ … This probability is independent of the measurement choices made by Bob and Charlie".

import Mathlib
import Definitions.Def_DrezetGHZ_Quantum

namespace DrezetGHZ
theorem ghz_nonsignaling :
    (∀ (n₁ n₂ n₃ n₂' n₃' : Setting) (α : ℤˣ),
      ∑ β, ∑ γ, bornProb n₁ n₂ n₃ α β γ = ∑ β, ∑ γ, bornProb n₁ n₂' n₃' α β γ) ∧
    (∀ (n₂ n₃ : Setting) (α : ℤˣ), ∑ β, ∑ γ, bornProb .x n₂ n₃ α β γ = 1 / 2) := by sorry
end DrezetGHZ
