-- Prove2me | Theorems.Thm_BudgetCoreExchange_theorem_4
-- name    : BudgetCoreExchange.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:10.454362+00:00
-- url     : https://prove2.me/theorems/b4764809-4a4d-4ad0-9215-22906fbaaac7
-- title:
--   Theorem 4: CEx$_\varphi$ has an $nW$-equilibrium iff $\exists x\forall y\,\varphi(x,y)$
-- statement:
--   Let $\varphi(x,y)$ be a DNF formula with $n\ge1$ $x$-variables, $m$ $y$-variables and $L$ terms, and let $T,U,V,W$ be any real constants with
--   $$
--   0\le T,\qquad nT<1,\qquad U>nL,\qquad V>4U,\qquad W>7nV .
--   $$
--   Then the exchange $\mathrm{CEx}_\varphi$ has a core outcome with welfare at least $nW$ (an $nW$-equilibrium) if and only if
--   $$
--   \exists x\in\{0,1\}^n\ \forall y\in\{0,1\}^m\ \ \varphi(x,y).
--   $$
--
--   This is the correctness of the reduction from QSAT$_2$: together with the polynomial size of $\mathrm{CEx}_\varphi$ it gives Theorem 2.
--
--   Differences from the source:
--   - reading: n ≥ 1 not stated → 1 ≤ n; reason: T < 1/n presupposes n ≥ 1
--   - reading: the printed bundle formulas of A.3 (T^{ψ,φ}_{li} = T^ψ_l ∪ {φ_li}, F^ψ_{li} = {ψ_{lii'}}, F^{ψ,φ}_l = T^{ψ,φ}_l ∪ …), the Bᴳ value (max{|G_l|,|Ḡ_l|} − 1)/(n(n+1)), Table 6's λ¹/λ̄¹ for B^{λ,2}, no seller values → T^{ψ,φ}_{li} = row {ψ_{lii'}} ∪ {φ_li}, F^ψ_{li} = column {ψ_{li'i}}, F^{ψ,φ}_l = whole matrix ∪ {φ_{l1..ln}}, Bᴳⱼ values the number of its clause bundles, B^{λ,2} values λ², λ̄², sellers value 0; reason: misprints resolved from Figure 2 (p.30), Figure 1 (p.27), the row/column description on p.28, the 'i.e.' on p.31 and the bullets on p.30; the transposed row/column reading gives an isomorphic exchange
--   - reading: T < 1/n → 0 ≤ T and nT < 1; reason: T is the budget Bᴷᵢ has left ('he only has a budget of T left', p.30), a nonnegative amount
--   - reading: (Core) d^C ≤ 0 for all C ⊂ I ∪ J → no nonempty coalition C ⊆ N (the grand coalition included) has an outcome feasible for C that strictly improves every member's payoff; reason: the text above (CEx) speaks of 'each coalition C ⊆ N' (p.11); the empty coalition would block vacuously; d^C > 0 iff every member can strictly gain
--   - encoding: package prices pᵢ(S), pⱼ(Z) with binary xᵢ(S), yⱼ(Z) and (XOR-B), (XOR-S) → one package Sᵢ (∅ = nothing) and one payment pᵢ per buyer, one package Zⱼ ⊆ K(j) and one receipt qⱼ per seller; reason: the paper notes the bilinear terms are a single variable pᵢ (pⱼ) (p.12); same instances
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Theorem 4, p.33 (Appendix A.4); constants p.29

import Mathlib
import Definitions.Def_BudgetCoreExchange_Exchange
import Definitions.Def_BudgetCoreExchange_InCore
import Definitions.Def_BudgetCoreExchange_QSAT2
import Definitions.Def_BudgetCoreExchange_gadget

namespace BudgetCoreExchange

/-- **Theorem 4** (Bichler–Waldherr, arXiv:1807.08253v1, Appendix A.4, p.33): "There exists an
nW-equilibrium if and only if ∃x∀yϕ(x,y) is true."

For every DNF formula `ϕ` with `n ≥ 1` `x`-variables and all admissible constants `T, U, V, W`
(`0 ≤ T`, `nT < 1`, `U > nL`, `V > 4U`, `W > 7nV`, p.29): the exchange `CEx_ϕ` has a core outcome
with welfare at least `nW` if and only if `∃x∀y ϕ(x, y)`.

**Formalization Note.** `n ≥ 1` is presupposed by the paper's `T < 1/n`. The constants are
arbitrary admissible reals. -/
theorem theorem_4 (ϕ : DNF) (hn : 1 ≤ ϕ.n) (T U V W : ℝ) (hA : Admissible ϕ T U V W) :
    (∃ o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ), IsNWEquilibrium ϕ T U V W o) ↔
      ϕ.QTrue := by sorry

end BudgetCoreExchange
