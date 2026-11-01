-- Prove2me | Theorems.Thm_BudgetCoreExchange_qsat2_polyReducible_coreWelfare
-- name    : BudgetCoreExchange.qsat2_polyReducible_coreWelfare
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:00.194815+00:00
-- url     : https://prove2.me/theorems/d14e32b3-764e-436a-b549-7c0e3125c205
-- title:
--   QSAT$_2$ reduces to CoreWelfare in polynomial time (Appendix A.3–A.4)
-- statement:
--   There is a polynomial-time many-one reduction from QSAT$_2$ to CoreWelfare: a function, computable in polynomial time by a Turing machine, that maps the code of every DNF formula $\varphi$ to the code of a rational exchange $E$ and a threshold $D$ such that
--   $$
--   \exists x\,\forall y\ \varphi(x,y)\iff E \text{ has a core outcome of welfare at least } D,
--   $$
--   and maps strings that are not codes of formulas to no-instances.
--
--   This is the reduction of Appendix A: $\varphi\mapsto(\mathrm{CEx}_\varphi, nW)$ with admissible rational constants.
--
--   **Formalization Note** The paper does not say "polynomial time" for its transformation; it is implicit in "a reduction from … QSAT$_2$".
--
--   Differences from the source:
--   - encoding: 'a reduction from … QSAT₂' (no model stated) → CookPvsNP.PolyReducible (polynomial-time many-one reduction, Cook's Turing machines); reason: the standard notion behind Σᵖ₂-hardness
--   - reading: arbitrary valuations vᵢ(S) ∈ ℝ≥0 with vᵢ(∅) = 0 and free disposal (pp.6–7); A.3's 'XOR bidding language' → valuations written in the 'XOR of additive groups' bid language (contains XOR bids), with nonnegative weights and nonempty bundles; reason: Theorem 2 fixes no input representation; A.3's own Bᴳ valuation has no polynomial-size XOR representation and is two groups
--   - encoding: real valuations, budgets and prices → rational instance data (values, budgets, threshold D) in binary over a 7-symbol alphabet; real payments; reason: a computational problem has finite inputs; prices stay real as in (CEx)
--   - reading: (Core) d^C ≤ 0 for all C ⊂ I ∪ J → no nonempty coalition C ⊆ N (the grand coalition included) has an outcome feasible for C that strictly improves every member's payoff; reason: the text above (CEx) speaks of 'each coalition C ⊆ N' (p.11); the empty coalition would block vacuously; d^C > 0 iff every member can strictly gain
--   - reading: (Imp-S) d^C ≤ Σ p^C_j(Z)γ^C_j(Z) − Σ p_j(Z)y_j(Z) (payments only) → a seller's improvement is measured in payoffs qⱼ − vⱼ(Zⱼ); reason: payoffs πⱼ = pⱼ(Z) − vⱼ(Z) (p.7) and 'the improvements for each individual buyer and seller' (p.12); identical when sellers value 0, as in the reduction
--   - encoding: package prices pᵢ(S), pⱼ(Z) with binary xᵢ(S), yⱼ(Z) and (XOR-B), (XOR-S) → one package Sᵢ (∅ = nothing) and one payment pᵢ per buyer, one package Zⱼ ⊆ K(j) and one receipt qⱼ per seller; reason: the paper notes the bilinear terms are a single variable pᵢ (pⱼ) (p.12); same instances
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Appendix A, p.27 ('a reduction from the canonical Σᵖ₂-complete problem QSAT₂'); A.3, pp.29–31 (construction); A.4, p.31

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_BudgetCoreExchange_QSAT2
import Definitions.Def_BudgetCoreExchange_CoreWelfare

namespace BudgetCoreExchange

/-- **The reduction QSAT₂ ≤ₚ CoreWelfare** (Bichler–Waldherr, arXiv:1807.08253v1, Appendix A,
p.27: "by a reduction from the canonical Σᵖ₂-complete problem QSAT₂", and A.3–A.4, pp.29–31: "For a
given formula ϕ(x,y) with clauses C1,...,CL construct an instance CExϕ(x,y) of a combinatorial
exchange …"; "there exists a core solution in CExϕ(x,y) with a social welfare of at least nW if and
only if ∃x∀yϕ(x,y) is true").

There is a polynomial-time computable map (Cook's Turing machines) sending the code of every DNF
formula `ϕ` to the code of a rational exchange with budgets and a threshold `D` such that
`∃x∀y ϕ(x, y)` holds iff the exchange has a core outcome of welfare at least `D` (and non-codes to
no-instances).

**Formalization Note.** The paper does not state that the transformation runs in polynomial time;
it is implicit in "a reduction". -/
theorem qsat2_polyReducible_coreWelfare : CookPvsNP.PolyReducible QSAT2 CoreWelfare := by sorry

end BudgetCoreExchange
