-- Prove2me | Theorems.Thm_ConstRegretMatch_Acyclic_lemma_C_1_U0
-- name    : ConstRegretMatch.Acyclic.lemma_C_1_U0
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:37:33.634723+00:00
-- url     : https://prove2.me/theorems/4365b8e7-2392-4fb7-9eb4-dfbc59518b00
-- title:
--   Lemma C.1, p. 44 (second sentence) — with ℳ₀ = ∅ and a connected acyclic residual graph, |𝒬₊| = n − d and |𝒰₀| ≥ 1
-- statement:
--   Let $(M, \lambda, r)$ be a matching network satisfying the general position condition, with unique non-degenerate optimal solution $(z^*, s^*)$ of (SPP). Assume the setting of Appendix C: there is a single component, i.e. no match is redundant ($\mathcal M_0 = \emptyset$), and the (SPP)-residual graph is connected and acyclic. Then
--   $$|\mathcal Q_+| = n - d \qquad\text{and}\qquad |\mathcal U_0| \ge 1,$$
--   where $\mathcal U_0 = \{i \in \mathcal Q_0 : \sum_{m} M_{im} = 1\}$ is the set of over-demanded queues taking part in exactly one match.
--
--   The non-empty set $\mathcal U_0$ supplies the endpoints of the paths along which Appendix C constructs the surplus vectors of Theorem 5.1.
--
--   **Formalization Note** $\mathcal M_0 = \emptyset$ and connectedness are the standing reduction of Appendix C ("we assume, without loss of generality, that there is a single component, i.e., $\mathcal M_0 = \emptyset$", p. 44) and are hypotheses here. $|\mathcal Q_+| = n - d$ is stated as $|\mathcal Q_+| + d = n$.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 44, App. C setting and Lemma C.1 (second sentence); proof p. 47

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network
import Definitions.Def_ConstRegretMatch_Acyclic_SPP
import Definitions.Def_ConstRegretMatch_Acyclic_Residual

namespace ConstRegretMatch.Acyclic

/-- Lemma C.1, p. 44 (second sentence), in the setting of App. C, p. 44 (a single component, i.e.
`ℳ₀ = ∅`): under GP with unique optimal solution `(z*, s*)`, if no match is redundant and the
(SPP)-residual graph is connected and acyclic, then `|𝒬₊| = n - d` and some over-demanded queue
participates in exactly one match: `|𝒰₀| ≥ 1`. -/
theorem lemma_C_1_U0 {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : ConstRegretMatch.Upper.IsMatchValues r) (lam : Fin n → ℝ) (hlam : ConstRegretMatch.Upper.IsArrivalRates lam)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s)
    (hM0 : ConstRegretMatch.Upper.Mzero z = ∅) (hconn : (residualGraph N z).Connected)
    (hacyc : (residualGraph N z).IsAcyclic) :
    (ConstRegretMatch.Upper.Qplus s).card + d = n ∧ 1 ≤ (U0 N s).card := by sorry

end ConstRegretMatch.Acyclic
