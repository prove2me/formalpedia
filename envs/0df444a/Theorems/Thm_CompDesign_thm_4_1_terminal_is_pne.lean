-- Prove2me | Theorems.Thm_CompDesign_thm_4_1_terminal_is_pne
-- name    : CompDesign.thm_4_1_terminal_is_pne
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:59:05.519511+00:00
-- url     : https://prove2.me/theorems/9f734b3b-6d73-4e36-aa4a-74f15fcf5184
-- title:
--   Proof of Theorem 4.1 — any terminal state is a pure Nash equilibrium
-- statement:
--   Let $v$ be any set function, $B$ any budget and $c$ any costs, and consider the game $\Gamma^{mc}$ with utilities $u_i(S)=p^{mc}_i(S)-c_i$ for $i\in S$ and $0$ otherwise. If $S$ is **terminal**, that is, no agent has a strict better response from $S$, then $S$ is a pure Nash equilibrium in the sense of Definition 3.1:
--   $$p^{mc}_i(S)-c_i\ge 0 \ \text{ for } i\in S, \qquad p^{mc}_i(S\cup\{i\})-c_i\le 0 \ \text{ for } i\notin S.$$
--
--   Together with termination, this gives the existence part of Theorem 4.1.
--
--   **Formalization Note** The pure Nash equilibrium is the published `CompDesignBFM.IsPNE`, which is Definition 3.1 for $p^{mc}$.
--
--   Differences from the source:
--   - generalization: Assumption 3.1, B > 0, c ≥ 0 and max_i c_i < B (the standing assumptions and the hypothesis of Theorem 4.1) → no hypotheses on v, B, c; reason: the implication from terminal to Definition 3.1 is a rewriting of the two cases of a switch and uses none of them; the paper's setting is an instance
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), proof of Theorem 4.1, §4.1, p.17 (PDF 20)

import Mathlib
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesign_IsStrictImprovement

open CompDesignBFM

namespace CompDesign

/-- Terminal states are equilibria, proof of Theorem 4.1, §4.1, p.17 (PDF 20) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…):
a set `S` from which no agent has a strict better response in `Γ^mc` is a pure Nash equilibrium
(Definition 3.1, p.14).

**Formalization Note.** The implication holds for every `v`, `B` and `c`, so the standing
assumptions are not binders. -/
theorem thm_4_1_terminal_is_pne {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) (h : ∀ S' : Finset (Fin n), ¬ IsStrictImprovement v B c S S') :
    IsPNE v B c S := by sorry

end CompDesign
