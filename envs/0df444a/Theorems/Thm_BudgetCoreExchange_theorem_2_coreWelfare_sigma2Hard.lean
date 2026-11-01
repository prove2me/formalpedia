-- Prove2me | Theorems.Thm_BudgetCoreExchange_theorem_2_coreWelfare_sigma2Hard
-- name    : BudgetCoreExchange.theorem_2_coreWelfare_sigma2Hard
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:17.864012+00:00
-- url     : https://prove2.me/theorems/3e2bfc7b-cfab-4796-87c7-d9c78f37e897
-- title:
--   Theorem 2: computing a welfare-maximizing core outcome in a budget-constrained combinatorial exchange is $\Sigma_2^p$-hard
-- statement:
--   Consider the decision problem **CoreWelfare**: given a combinatorial exchange with budget-constrained buyers (rational valuations, budgets and endowments) and a rational threshold $D$, does the exchange have a **core outcome** whose welfare (gains from trade) is at least $D$? Here outcomes satisfy budget constraints $p_i\le\min\{B_i,v_i(S_i)\}$, individual rationality of sellers, budget balance and supply, and an outcome is in the core if no nonempty coalition can strictly improve all its members using only its own items and money.
--
--   **Theorem.** CoreWelfare is $\Sigma_2^p$-hard: every language in $\Sigma_2^p$, over any finite nonempty alphabet, reduces to CoreWelfare by a polynomial-time many-one reduction.
--
--   This is Theorem 2 of the paper: in the presence of budget constraints, core pricing in combinatorial exchanges sits at the second level of the polynomial hierarchy, above the NP-hard allocation problem.
--
--   **Formalization Note** The exchange model is the bilevel program (CEx) with one package and one payment per agent; valuations are given in the "XOR of additive groups" bid language; payments are real.
--
--   Differences from the source:
--   - reading: 'Computing a welfare-maximizing core outcome … is Σᵖ₂-hard' → deciding whether some core outcome has welfare ≥ D is Σᵖ₂-hard (Sigma2Hard CoreWelfare); reason: Appendix A states and proves the problem in this form (A.1, p.27; A.4, p.31)
--   - encoding: Σᵖ₂-hardness (no machine model stated) → every Σᵖ₂ language (∃∀ form, |w|^k certificate bounds, checking language in CookPvsNP.P) over every finite nonempty alphabet ≤ₚ-reduces to the language, in Cook's Turing-machine model; reason: standard definition (Arora–Barak Def. 5.1) on the platform's CookPvsNP framework
--   - reading: arbitrary valuations vᵢ(S) ∈ ℝ≥0 with vᵢ(∅) = 0 and free disposal (pp.6–7); A.3's 'XOR bidding language' → valuations written in the 'XOR of additive groups' bid language (contains XOR bids), with nonnegative weights and nonempty bundles; reason: Theorem 2 fixes no input representation; A.3's own Bᴳ valuation has no polynomial-size XOR representation and is two groups
--   - reading: (Core) d^C ≤ 0 for all C ⊂ I ∪ J → no nonempty coalition C ⊆ N (the grand coalition included) has an outcome feasible for C that strictly improves every member's payoff; reason: the text above (CEx) speaks of 'each coalition C ⊆ N' (p.11); the empty coalition would block vacuously; d^C > 0 iff every member can strictly gain
--   - reading: (Imp-S) d^C ≤ Σ p^C_j(Z)γ^C_j(Z) − Σ p_j(Z)y_j(Z) (payments only) → a seller's improvement is measured in payoffs qⱼ − vⱼ(Zⱼ); reason: payoffs πⱼ = pⱼ(Z) − vⱼ(Z) (p.7) and 'the improvements for each individual buyer and seller' (p.12); identical when sellers value 0, as in the reduction
--   - encoding: package prices pᵢ(S), pⱼ(Z) with binary xᵢ(S), yⱼ(Z) and (XOR-B), (XOR-S) → one package Sᵢ (∅ = nothing) and one payment pᵢ per buyer, one package Zⱼ ⊆ K(j) and one receipt qⱼ per seller; reason: the paper notes the bilinear terms are a single variable pᵢ (pⱼ) (p.12); same instances
--   - encoding: real valuations, budgets and prices → rational instance data (values, budgets, threshold D) in binary over a 7-symbol alphabet; real payments; reason: a computational problem has finite inputs; prices stay real as in (CEx)
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Theorem 2, p.9; decision form in Appendix A, A.1 p.27 and A.4 p.31

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_BudgetCoreExchange_Sigma2P
import Definitions.Def_BudgetCoreExchange_CoreWelfare

namespace BudgetCoreExchange

/-- **Theorem 2** (Bichler–Waldherr, arXiv:1807.08253v1, §3.1, p.9): "Computing a welfare-maximizing
core outcome in a combinatorial exchange with budget constraint is Σᵖ₂-hard".

Stated in its decision form (Appendix A, A.1 p.27 and A.4 p.31): every Σᵖ₂ language over every
finite nonempty alphabet reduces in polynomial time (Cook's `≤ₚ`) to `CoreWelfare`, the language of
codes of pairs `(E, D)` of a combinatorial exchange with budget-constrained buyers and a welfare
threshold such that some core outcome of `E` has welfare at least `D`.

**Formalization Note.**
* The exchange model is the program (CEx), p.11: one package and one payment per agent, (BC)
  `p ≤ min(B, v(S))`, (IRS), aggregate (BB), (Supply), sellers selling endowed items; the core is
  blocked by no nonempty coalition (grand coalition included) whose members all strictly gain.
* Instances have rational data in binary and valuations in the "XOR of additive groups" bid
  language; payments are real. -/
theorem theorem_2_coreWelfare_sigma2Hard : Sigma2Hard CoreWelfare := by sorry

end BudgetCoreExchange
