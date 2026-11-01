-- Prove2me | Theorems.Thm_BudgetCoreExchange_lemma_4
-- name    : BudgetCoreExchange.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:28.796025+00:00
-- url     : https://prove2.me/theorems/7a78cd7a-e8d8-47e3-8546-489e179284b5
-- title:
--   Lemma 4: in any core outcome the $B^{\mathcal G}$ buyers collect as many unblocked falsifiable clauses as possible
-- statement:
--   Let $\varphi$ be a DNF formula with $n\ge1$ $x$-variables, $m$ $y$-variables and $L$ terms, let $T,U,V,W$ be admissible, and let $o$ be **any** core outcome of $\mathrm{CEx}_\varphi$. Write $\beta_l$ for "no $B^{\mathcal M}_i$ obtains a column $\mathcal F^\psi_{li}$ of clause $l$ in $o$". Then the combined size of the clean bundles of the buyers $B^{\mathcal G}_j$, i.e. the sum of their valuations, equals
--   $$
--   \sum_{j=1}^m v_{B^{\mathcal G}_j}(S_{B^{\mathcal G}_j})=\max_{y\in\{0,1\}^m}\#\{\,l\le L:\ \beta_l \text{ and some } y\text{-literal of } C_l \text{ is false under } y\,\}.
--   $$
--
--   This is Lemma 4 of the paper: the buyers $B^{\mathcal G}$ play the universal player of QSAT$_2$, falsifying as many clauses as an assignment $y$ can among those the $x$-assignment has not already falsified.
--
--   **Formalization Note** A clean bundle of size $k$ is a package worth $k$ to $B^{\mathcal G}_j$ (p.31). The maximum over the allocations of the unblocked bundles $\mathcal F^{\psi,\phi}_l$ to the buyers $B^{\mathcal G}$ is written as the maximum over $y$: $B^{\mathcal G}_j$ holding $\gamma_j$ ($y_j$ true) collects the clauses containing $\bar y_j$, holding $\bar\gamma_j$ those containing $y_j$, and each $\mathcal F^{\psi,\phi}_l$ has one supplier.
--
--   Differences from the source:
--   - reading: 'buyers of type Bᴳ maximize the combined size of their clean bundles among the ones not blocked by buyers of type Bᴹ' → Σⱼ v_{Bᴳⱼ}(S_{Bᴳⱼ}) = max over y of #{l : C_l not blocked by Bᴹ in o and falsified by y}; reason: the combined clean size is the sum of the Bᴳ valuations (p.31); the achievable maxima over Bᴳ allocations of unblocked clause bundles are exactly these counts
--   - reading: n ≥ 1 not stated → 1 ≤ n; reason: T < 1/n presupposes n ≥ 1
--   - reading: the printed bundle formulas of A.3 (T^{ψ,φ}_{li} = T^ψ_l ∪ {φ_li}, F^ψ_{li} = {ψ_{lii'}}, F^{ψ,φ}_l = T^{ψ,φ}_l ∪ …), the Bᴳ value (max{|G_l|,|Ḡ_l|} − 1)/(n(n+1)), Table 6's λ¹/λ̄¹ for B^{λ,2}, no seller values → T^{ψ,φ}_{li} = row {ψ_{lii'}} ∪ {φ_li}, F^ψ_{li} = column {ψ_{li'i}}, F^{ψ,φ}_l = whole matrix ∪ {φ_{l1..ln}}, Bᴳⱼ values the number of its clause bundles, B^{λ,2} values λ², λ̄², sellers value 0; reason: misprints resolved from Figure 2 (p.30), Figure 1 (p.27), the row/column description on p.28, the 'i.e.' on p.31 and the bullets on p.30; the transposed row/column reading gives an isomorphic exchange
--   - reading: T < 1/n → 0 ≤ T and nT < 1; reason: T is the budget Bᴷᵢ has left ('he only has a budget of T left', p.30), a nonnegative amount
--   - reading: (Core) d^C ≤ 0 for all C ⊂ I ∪ J → no nonempty coalition C ⊆ N (the grand coalition included) has an outcome feasible for C that strictly improves every member's payoff; reason: the text above (CEx) speaks of 'each coalition C ⊆ N' (p.11); the empty coalition would block vacuously; d^C > 0 iff every member can strictly gain
--   - encoding: package prices pᵢ(S), pⱼ(Z) with binary xᵢ(S), yⱼ(Z) and (XOR-B), (XOR-S) → one package Sᵢ (∅ = nothing) and one payment pᵢ per buyer, one package Zⱼ ⊆ K(j) and one receipt qⱼ per seller; reason: the paper notes the bilinear terms are a single variable pᵢ (pⱼ) (p.12); same instances
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Lemma 4, p.33 (Appendix A.4; announced on p.31)

import Mathlib
import Definitions.Def_BudgetCoreExchange_Exchange
import Definitions.Def_BudgetCoreExchange_InCore
import Definitions.Def_BudgetCoreExchange_QSAT2
import Definitions.Def_BudgetCoreExchange_gadget

namespace BudgetCoreExchange

open Classical in
/-- **Lemma 4** (Bichler–Waldherr, arXiv:1807.08253v1, Appendix A.4, p.33): "In any core
allocation, buyers of type Bᴳ maximize the combined size of their clean bundles among the ones not
blocked by buyers of type Bᴹ."

For every DNF formula `ϕ` with `n ≥ 1`, all admissible constants (p.29) and **every core outcome**
`o` of `CEx_ϕ`, the combined value `Σⱼ v_{Bᴳⱼ}(Sⱼ)` of the buyers `Bᴳⱼ` (the combined size of their
clean bundles) equals the largest number of clauses that are not blocked by `Bᴹ` in `o` and can be
falsified by one truth assignment `y` of the `y`-variables:
`max_y #{l : C_l not blocked by Bᴹ in o, and some y-literal of C_l is false under y}`.

**Formalization Note.** A clean bundle of size `k` is a package worth `k` to `Bᴳⱼ` (p.31), so the
combined size is the sum of the `Bᴳ` valuations. The maximum over the clean-bundle allocations
of the unblocked clause bundles `F^{ψ,φ}_l` is written as the maximum over the assignments `y`
(`Bᴳⱼ` holding `γⱼ` collects the clauses with `ȳⱼ`, holding `γ̄ⱼ` those with `yⱼ`, and each
`F^{ψ,φ}_l` goes to at most one buyer). -/
theorem lemma_4 (ϕ : DNF) (hn : 1 ≤ ϕ.n) (T U V W : ℝ) (hA : Admissible ϕ T U V W)
    (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (ho : InCore (gadget ϕ T U V W) o) :
    ∑ j : Fin ϕ.m, (gadget ϕ T U V W).bval (Gadget.BG j) (o.S (Gadget.BG j)) =
      ((Finset.univ.sup fun y : Fin ϕ.m → Bool =>
          (Finset.univ.filter fun l : Fin ϕ.numTerms =>
            ¬ BlockedByM o l ∧ FalsifiedBy y l).card : ℕ) : ℝ) := by sorry

end BudgetCoreExchange
