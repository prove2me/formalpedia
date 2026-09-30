-- Prove2me | Theorems.Thm_DrezetGHZ_local_causality_implies_nonsignaling
-- name    : DrezetGHZ.local_causality_implies_nonsignaling
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T20:49:15.786118+00:00
-- url     : https://prove2.me/theorems/b02ab3ad-06f1-4726-ae4d-bca71bc1dfce
-- title:
--   Local causality implies non-signalling
-- statement:
--   Let $M$ be a locally causal model (Eqs. (14), (17), (18)). For every setting $\hat n_1$ of Alice, every outcome $\alpha$, and any two choices $(\hat n_2,\hat n_3)$ and $(\hat n_2',\hat n_3')$ of Bob's and Charlie's settings,
--   $$\sum_{\beta,\gamma=\pm1}P(\alpha,\beta,\gamma\mid\hat n_1,\hat n_2,\hat n_3)=\sum_{\beta,\gamma=\pm1}P(\alpha,\beta,\gamma\mid\hat n_1,\hat n_2',\hat n_3').$$
--
--   Alice's marginal statistics therefore do not depend on the distant settings. The paper uses this to argue that non-signalling cannot distinguish local causality from quantum mechanics.
-- source:
--   A. Drezet, "An Elementary Proof That Everett's Quantum Multiverse Is Nonlocal: Bell-Locality and Branch-Symmetry in the Many-Worlds Interpretation", arXiv:2306.07794v1 [quant-ph] (2023), https://arxiv.org/abs/2306.07794, p. 10: "Clearly, local-causality implies nonsignaling, but the opposite is not always true" (following Eq. (29)).

import Mathlib
import Definitions.Def_DrezetGHZ_Models

namespace DrezetGHZ
theorem local_causality_implies_nonsignaling {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalCausalModel Λ) (n₁ n₂ n₃ n₂' n₃' : Setting) (α : ℤˣ) :
    ∑ β, ∑ γ, M.predict n₁ n₂ n₃ α β γ = ∑ β, ∑ γ, M.predict n₁ n₂' n₃' α β γ := by sorry
end DrezetGHZ
