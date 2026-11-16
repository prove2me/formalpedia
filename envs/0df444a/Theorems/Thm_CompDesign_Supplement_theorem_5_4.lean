-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_5_4
-- name    : CompDesign.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:55:36.437013+00:00
-- url     : https://prove2.me/theorems/4e8fb229-8e7b-4625-9f60-f0deaa25c5b7
-- title:
--   Theorem 5.4 — the 1/3 singleton-prize, 2/3 marginal-contribution rule has $\mathbb E[v(S)]\ge\mathrm{OPT}/3$ for any costs
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget and $c_i\ge0$ the private costs. the value function $v$ satisfies Assumption 3.1: $v(\emptyset)=0$, $v$ is monotone and submodular. No large-market assumption is made: costs may be as large as or larger than $B$. The randomized rule plays the singleton-prize rule $p^{sing}$ (for a fixed priority order) with probability $1/3$ and the marginal-contribution rule $p^{mc}$ with probability $2/3$; in each branch the agents play a principal-favoring pure Nash equilibrium.
--
--   **Theorem 5.4 (Constant PoA without a large-market assumption).** For every strict priority order, every principal-favoring pure Nash equilibrium $S_{sing}$ of $p^{sing}$ and every principal-favoring pure Nash equilibrium $S_{mc}$ of $p^{mc}$,
--   $$\tfrac13v(S_{sing})+\tfrac23v(S_{mc})\ \ge\ \tfrac13\,\mathrm{OPT}.$$
--   The expected pure price of anarchy of this rule is therefore at most 3.
--
--   This contrasts with the $\sqrt{n-1}$ lower bound for deterministic rules (Theorem 5.3).
--
--   Differences from the source:
--   - encoding: a fixed public priority order → any injective rank prio : Fin n → ℕ; the statement holds for every one; reason: a strict order is the same as an injective rank up to relabelling
--   - encoding: E[v(S)] ≥ OPT/3 under every branch-contingent principal-favoring PNE → OPT/3 ≤ v(S_sing)/3 + 2·v(S_mc)/3 for every pair of principal-favoring PNE of the two branches; reason: the expectation over the two branches with probabilities 1/3 and 2/3
--   - encoding: "the expected pure price of anarchy is at most 3" → no separate clause; reason: it is the displayed inequality restated
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 5.4, §5.3, p.34 (PDF 37)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsPNEOf
import Definitions.Def_CompDesign_Supplement_singletonPay

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 5.4 (Constant PoA without a large-market assumption), §5.3, p.34 (PDF 37) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). For
every normalized monotone submodular value function `v` and every budget `B > 0`, the randomized
rule (singleton-prize branch with probability 1/3, marginal-contribution branch with probability
2/3) satisfies `E[v(S)] ≥ OPT/3` under every branch-contingent principal-favoring pure Nash
equilibrium.

**Formalization Note.** No large-market hypothesis: the costs are any `c ≥ 0`, including `c_i ≥ B`.
The singleton-prize branch is `singletonPay` for a fixed public priority order, an injective rank
`prio`; the statement holds for every such order. A branch-contingent equilibrium is a pair
`(S_sing, S_mc)` of principal-favoring pure Nash equilibria of the two branches, and
`E[v(S)] = (1/3) v(S_sing) + (2/3) v(S_mc)`. -/
theorem theorem_5_4 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (prio : Fin n → ℕ) (hprio : Function.Injective prio) (Ssing Smc : Finset (Fin n))
    (hsing : IsPFPNEOf (singletonPay v B prio) v c Ssing)
    (hmc : IsPFPNEOf (mcPay v B) v c Smc) :
    OPT v B c / 3 ≤ v Ssing / 3 + 2 * v Smc / 3 := by sorry

end CompDesign.Supplement
