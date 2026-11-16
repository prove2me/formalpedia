-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_4_2
-- name    : CompDesign.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:53:07.867384+00:00
-- url     : https://prove2.me/theorems/efc53932-820a-41cb-8ed6-d47c7258fb14
-- title:
--   Theorem 4.2 — Shapley payments: four-agent instances with no pure Nash equilibrium for every $\bar\lambda>0$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget and $c_i\ge0$ the private costs. The Shapley payment rule is $p^{Sh}_i(S)=B\varphi_i(S)/v(S)$ for $i\in S$ with $v(S)>0$ and $0$ otherwise (7).
--
--   **Theorem 4.2 (Nonexistence of pure Nash equilibria under Shapley payments).** For every $\bar\lambda>0$ there are a budget $B>0$, a value function $v$ on four agents that is normalized, monotone and submodular, and costs with
--   $$0<c_i\le\bar\lambda B\qquad(i=1,\dots,4)$$
--   such that the game induced by $p^{Sh}$ has no pure Nash equilibrium: no $S\subseteq N$ satisfies $p^{Sh}_i(S)\ge c_i$ for all $i\in S$ and $p^{Sh}_i(S\cup\{i\})\le c_i$ for all $i\notin S$.
--
--   Shapley payments are anonymous, budget feasible and 1-marginal-covering, yet unlike the marginal-contribution rule they need not admit a pure equilibrium, however small the costs relative to the budget.
--
--   Differences from the source:
--   - encoding: max_{i∈N} c_i/B ≤ λ̄ → c_i ≤ λ̄·B for every i; reason: equivalent for B > 0
--   - encoding: a monotone submodular value function → v ∅ = 0, monotone and submodular; reason: normalization is part of Assumption 3.1, the standing assumption of §§3–5; the instance satisfies it
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 4.2, §4.2.1, p.18 (PDF 21)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesign_Supplement_IsPNEOf
import Definitions.Def_CompDesign_Supplement_shapleyPay

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 4.2 (Nonexistence of pure Nash equilibria under Shapley payments), §4.2.1, p.18
(PDF 21) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). For every `λ̄ > 0`, there is an instance with four agents, a monotone submodular
value function, and strictly positive costs satisfying `max_i c_i/B ≤ λ̄` such that the game induced
by `p^Sh` per (7) has no pure Nash equilibrium.

**Formalization Note.** `λ̄` is `lbar`; `max_i c_i/B ≤ λ̄` is `c_i ≤ λ̄ B` for every `i`. The value
function satisfies Assumption 3.1 (normalized, monotone, submodular), hence is nonnegative. The
Shapley payments are `shapleyPay` (7), and the pure Nash equilibrium is Definition 3.1 for that rule. -/
theorem theorem_4_2 (lbar : ℝ) (hl : 0 < lbar) :
    ∃ (v : Finset (Fin 4) → ℝ) (B : ℝ) (c : Fin 4 → ℝ), 0 < B ∧ v ∅ = 0 ∧ IsMonotoneSF v ∧
      IsSubmodularSF v ∧ (∀ i, 0 < c i ∧ c i ≤ lbar * B) ∧
      ∀ S : Finset (Fin 4), ¬ IsPNEOf (shapleyPay v B) c S := by sorry

end CompDesign.Supplement
