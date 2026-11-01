-- Prove2me | Theorems.Thm_BudgetCoreExchange_lemma_1
-- name    : BudgetCoreExchange.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:52.164352+00:00
-- url     : https://prove2.me/theorems/33f3c0e6-2982-4b09-9b2a-5326f48e2c1f
-- title:
--   Lemma 1: in an $nW$-equilibrium every $B^{\mathcal K}_i$ obtains a bundle it values at $W$
-- statement:
--   Let $\varphi$ be a DNF formula with $n$ $x$-variables, $m$ $y$-variables and $L$ terms, let $T,U,V,W$ be admissible constants ($0\le T$, $nT<1$, $U>nL$, $V>4U$, $W>7nV$), and let $o$ be an $nW$-equilibrium of the exchange $\mathrm{CEx}_\varphi$, i.e. a core outcome with welfare at least $nW$. Then for every $i$ the package of $B^{\mathcal K}_i$ contains $\mathcal K_l=\{\chi_i\}\cup\mathcal T^{\psi,\phi}_{li}$ or $\bar{\mathcal K}_l=\{\bar\chi_i\}\cup\mathcal T^{\psi,\phi}_{li}$ for some clause $l$.
--
--   This is Lemma 1 of the paper, one of the steps showing that an $nW$-equilibrium encodes a truth assignment of $x$ (Theorem 4).
--
--   Differences from the source:
--   - reading: a buyer 'obtains' a bundle → the bundle is contained in the package the buyer receives; reason: each buyer receives one package (XOR-B) and has free disposal (p.7)
--   - reading: the printed bundle formulas of A.3 (T^{ψ,φ}_{li} = T^ψ_l ∪ {φ_li}, F^ψ_{li} = {ψ_{lii'}}, F^{ψ,φ}_l = T^{ψ,φ}_l ∪ …), the Bᴳ value (max{|G_l|,|Ḡ_l|} − 1)/(n(n+1)), Table 6's λ¹/λ̄¹ for B^{λ,2}, no seller values → T^{ψ,φ}_{li} = row {ψ_{lii'}} ∪ {φ_li}, F^ψ_{li} = column {ψ_{li'i}}, F^{ψ,φ}_l = whole matrix ∪ {φ_{l1..ln}}, Bᴳⱼ values the number of its clause bundles, B^{λ,2} values λ², λ̄², sellers value 0; reason: misprints resolved from Figure 2 (p.30), Figure 1 (p.27), the row/column description on p.28, the 'i.e.' on p.31 and the bullets on p.30; the transposed row/column reading gives an isomorphic exchange
--   - reading: T < 1/n → 0 ≤ T and nT < 1; reason: T is the budget Bᴷᵢ has left ('he only has a budget of T left', p.30), a nonnegative amount
--   - reading: (Core) d^C ≤ 0 for all C ⊂ I ∪ J → no nonempty coalition C ⊆ N (the grand coalition included) has an outcome feasible for C that strictly improves every member's payoff; reason: the text above (CEx) speaks of 'each coalition C ⊆ N' (p.11); the empty coalition would block vacuously; d^C > 0 iff every member can strictly gain
--   - encoding: package prices pᵢ(S), pⱼ(Z) with binary xᵢ(S), yⱼ(Z) and (XOR-B), (XOR-S) → one package Sᵢ (∅ = nothing) and one payment pᵢ per buyer, one package Zⱼ ⊆ K(j) and one receipt qⱼ per seller; reason: the paper notes the bilinear terms are a single variable pᵢ (pⱼ) (p.12); same instances
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Lemma 1, p.32 (Appendix A.4; announced on p.31)

import Mathlib
import Definitions.Def_BudgetCoreExchange_Exchange
import Definitions.Def_BudgetCoreExchange_InCore
import Definitions.Def_BudgetCoreExchange_QSAT2
import Definitions.Def_BudgetCoreExchange_gadget

namespace BudgetCoreExchange

/-- **Lemma 1** (Bichler–Waldherr, arXiv:1807.08253v1, Appendix A.4, p.32): "In an nW-equilibrium,
for each i = 1,...,n, buyer Bᴷᵢ obtains one of the bundles he values at W."

For every DNF formula `ϕ`, all admissible constants `T, U, V, W` (p.29), every `nW`-equilibrium
`o` of `CEx_ϕ` and every `i`, the package of `Bᴷᵢ` contains `K_l = {χᵢ} ∪ T^{ψ,φ}_{li}` or
`K̄_l = {χ̄ᵢ} ∪ T^{ψ,φ}_{li}` for some clause `l`.

**Formalization Note.** "Obtains a bundle" means the bundle is contained in the package the buyer
receives (free disposal); this is the same as the buyer's value being `W`. -/
theorem lemma_1 (ϕ : DNF) (T U V W : ℝ) (hA : Admissible ϕ T U V W)
    (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (ho : IsNWEquilibrium ϕ T U V W o)
    (i : Fin ϕ.n) :
    ∃ l : Fin ϕ.numTerms,
      Gadget.Kb l i ⊆ o.S (Gadget.BK i) ∨ Gadget.Kbar l i ⊆ o.S (Gadget.BK i) := by sorry

end BudgetCoreExchange
