-- Prove2me | Theorems.Thm_BudgetCoreExchange_lemma_3
-- name    : BudgetCoreExchange.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:03.06758+00:00
-- url     : https://prove2.me/theorems/48adde18-a0f8-42e1-95af-1ff2215e860b
-- title:
--   Lemma 3: in an $nW$-equilibrium $B^{\mathcal M}_i$ obtains $\mathcal M_i$ or $\bar{\mathcal M}_i$
-- statement:
--   Let $\varphi$ be a DNF formula with $n$ $x$-variables, $m$ $y$-variables and $L$ terms, let $T,U,V,W$ be admissible constants ($0\le T$, $nT<1$, $U>nL$, $V>4U$, $W>7nV$), and let $o$ be an $nW$-equilibrium of the exchange $\mathrm{CEx}_\varphi$, i.e. a core outcome with welfare at least $nW$. Then for every $i$ the package of $B^{\mathcal M}_i$ contains one of his bundles
--   $$
--   \mathcal M_i=\{\chi_i,\lambda^1_i,\lambda^2_i\}\cup\bigcup_{x_i\in C_l}\mathcal F^\psi_{li}\quad\text{or}\quad \bar{\mathcal M}_i=\{\bar\chi_i,\bar\lambda^1_i,\bar\lambda^2_i\}\cup\bigcup_{\bar x_i\in C_l}\mathcal F^\psi_{li}.
--   $$
--
--   This is Lemma 3 of the paper, one of the steps showing that an $nW$-equilibrium encodes a truth assignment of $x$ (Theorem 4).
--
--   Differences from the source:
--   - reading: 'obtains all his required items from sellers Sψ and Sλ' → the package of Bᴹᵢ contains Mᵢ or M̄ᵢ; reason: the required items are those of the bundle he values (p.30); the χ-item it contains is the one Lemma 2 gives him, so this is the same claim
--   - reading: a buyer 'obtains' a bundle → the bundle is contained in the package the buyer receives; reason: each buyer receives one package (XOR-B) and has free disposal (p.7)
--   - reading: the printed bundle formulas of A.3 (T^{ψ,φ}_{li} = T^ψ_l ∪ {φ_li}, F^ψ_{li} = {ψ_{lii'}}, F^{ψ,φ}_l = T^{ψ,φ}_l ∪ …), the Bᴳ value (max{|G_l|,|Ḡ_l|} − 1)/(n(n+1)), Table 6's λ¹/λ̄¹ for B^{λ,2}, no seller values → T^{ψ,φ}_{li} = row {ψ_{lii'}} ∪ {φ_li}, F^ψ_{li} = column {ψ_{li'i}}, F^{ψ,φ}_l = whole matrix ∪ {φ_{l1..ln}}, Bᴳⱼ values the number of its clause bundles, B^{λ,2} values λ², λ̄², sellers value 0; reason: misprints resolved from Figure 2 (p.30), Figure 1 (p.27), the row/column description on p.28, the 'i.e.' on p.31 and the bullets on p.30; the transposed row/column reading gives an isomorphic exchange
--   - reading: T < 1/n → 0 ≤ T and nT < 1; reason: T is the budget Bᴷᵢ has left ('he only has a budget of T left', p.30), a nonnegative amount
--   - reading: (Core) d^C ≤ 0 for all C ⊂ I ∪ J → no nonempty coalition C ⊆ N (the grand coalition included) has an outcome feasible for C that strictly improves every member's payoff; reason: the text above (CEx) speaks of 'each coalition C ⊆ N' (p.11); the empty coalition would block vacuously; d^C > 0 iff every member can strictly gain
--   - encoding: package prices pᵢ(S), pⱼ(Z) with binary xᵢ(S), yⱼ(Z) and (XOR-B), (XOR-S) → one package Sᵢ (∅ = nothing) and one payment pᵢ per buyer, one package Zⱼ ⊆ K(j) and one receipt qⱼ per seller; reason: the paper notes the bilinear terms are a single variable pᵢ (pⱼ) (p.12); same instances
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Lemma 3, p.32 (Appendix A.4; announced on p.31)

import Mathlib
import Definitions.Def_BudgetCoreExchange_Exchange
import Definitions.Def_BudgetCoreExchange_InCore
import Definitions.Def_BudgetCoreExchange_QSAT2
import Definitions.Def_BudgetCoreExchange_gadget

namespace BudgetCoreExchange

/-- **Lemma 3** (Bichler–Waldherr, arXiv:1807.08253v1, Appendix A.4, p.32): "In an
nW-equilibrium, for i = 1,...,n buyer Bᴹᵢ obtains all his required items from sellers Sψ and Sλ."

For every DNF formula `ϕ`, all admissible constants (p.29), every `nW`-equilibrium `o` of `CEx_ϕ`
and every `i`, the package of `Bᴹᵢ` contains one of his bundles
`Mᵢ = {χᵢ, λ¹ᵢ, λ²ᵢ} ∪ ⋃_{xᵢ ∈ C_l} F^ψ_{li}` or `M̄ᵢ = {χ̄ᵢ, λ̄¹ᵢ, λ̄²ᵢ} ∪ ⋃_{x̄ᵢ ∈ C_l} F^ψ_{li}`.

**Formalization Note.** "All his required items" are the items of one of the two bundles `Bᴹᵢ`
values (p.30); with Lemma 2, it is the one whose `χ`-item is not held by `Bᴷᵢ`. -/
theorem lemma_3 (ϕ : DNF) (T U V W : ℝ) (hA : Admissible ϕ T U V W)
    (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (ho : IsNWEquilibrium ϕ T U V W o)
    (i : Fin ϕ.n) :
    Gadget.Mb i ⊆ o.S (Gadget.BM i) ∨ Gadget.Mbar i ⊆ o.S (Gadget.BM i) := by sorry

end BudgetCoreExchange
