-- Prove2me | Theorems.Thm_BudgetCoreExchange_lemma_2
-- name    : BudgetCoreExchange.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:43.854954+00:00
-- url     : https://prove2.me/theorems/76e64526-bb61-43c9-9c9c-fa29aebd94cb
-- title:
--   Lemma 2: in an $nW$-equilibrium $B^{\mathcal K}_i$ and $B^{\mathcal M}_i$ split $\chi_i,\bar\chi_i$ and $S^\chi_i$ receives at least $2V$
-- statement:
--   Let $\varphi$ be a DNF formula with $n$ $x$-variables, $m$ $y$-variables and $L$ terms, let $T,U,V,W$ be admissible constants ($0\le T$, $nT<1$, $U>nL$, $V>4U$, $W>7nV$), and let $o$ be an $nW$-equilibrium of the exchange $\mathrm{CEx}_\varphi$, i.e. a core outcome with welfare at least $nW$. Then for every $i$, either $\chi_i$ is in the package of $B^{\mathcal K}_i$ and $\bar\chi_i$ in that of $B^{\mathcal M}_i$, or the other way round; and the seller $S^\chi_i$ receives
--   $$
--   q(S^\chi_i)\ \ge\ 2V.
--   $$
--
--   This is Lemma 2 of the paper, one of the steps showing that an $nW$-equilibrium encodes a truth assignment of $x$ (Theorem 4).
--
--   Differences from the source:
--   - reading: items χ¹ᵢ, χ̄¹ᵢ → items χᵢ, χ̄ᵢ; reason: no items χ¹ᵢ exist; A.3 defines χᵢ, χ̄ᵢ (p.29)
--   - reading: 'both pay V to Sχᵢ' → the receipt of Sχᵢ is at least 2V; reason: (CEx) has one payment per agent and aggregate budget balance, so bilateral payments are undefined; the proof shows the lower bound ('If either Bᴷᵢ or Bᴹᵢ would pay less than V, then either Bχ,1ᵢ or Bχ,2ᵢ could outbid them')
--   - reading: a buyer 'obtains' a bundle → the bundle is contained in the package the buyer receives; reason: each buyer receives one package (XOR-B) and has free disposal (p.7)
--   - reading: the printed bundle formulas of A.3 (T^{ψ,φ}_{li} = T^ψ_l ∪ {φ_li}, F^ψ_{li} = {ψ_{lii'}}, F^{ψ,φ}_l = T^{ψ,φ}_l ∪ …), the Bᴳ value (max{|G_l|,|Ḡ_l|} − 1)/(n(n+1)), Table 6's λ¹/λ̄¹ for B^{λ,2}, no seller values → T^{ψ,φ}_{li} = row {ψ_{lii'}} ∪ {φ_li}, F^ψ_{li} = column {ψ_{li'i}}, F^{ψ,φ}_l = whole matrix ∪ {φ_{l1..ln}}, Bᴳⱼ values the number of its clause bundles, B^{λ,2} values λ², λ̄², sellers value 0; reason: misprints resolved from Figure 2 (p.30), Figure 1 (p.27), the row/column description on p.28, the 'i.e.' on p.31 and the bullets on p.30; the transposed row/column reading gives an isomorphic exchange
--   - reading: T < 1/n → 0 ≤ T and nT < 1; reason: T is the budget Bᴷᵢ has left ('he only has a budget of T left', p.30), a nonnegative amount
--   - reading: (Core) d^C ≤ 0 for all C ⊂ I ∪ J → no nonempty coalition C ⊆ N (the grand coalition included) has an outcome feasible for C that strictly improves every member's payoff; reason: the text above (CEx) speaks of 'each coalition C ⊆ N' (p.11); the empty coalition would block vacuously; d^C > 0 iff every member can strictly gain
--   - encoding: package prices pᵢ(S), pⱼ(Z) with binary xᵢ(S), yⱼ(Z) and (XOR-B), (XOR-S) → one package Sᵢ (∅ = nothing) and one payment pᵢ per buyer, one package Zⱼ ⊆ K(j) and one receipt qⱼ per seller; reason: the paper notes the bilinear terms are a single variable pᵢ (pⱼ) (p.12); same instances
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Lemma 2, p.32 (Appendix A.4; announced on p.31)

import Mathlib
import Definitions.Def_BudgetCoreExchange_Exchange
import Definitions.Def_BudgetCoreExchange_InCore
import Definitions.Def_BudgetCoreExchange_QSAT2
import Definitions.Def_BudgetCoreExchange_gadget

namespace BudgetCoreExchange

/-- **Lemma 2** (Bichler–Waldherr, arXiv:1807.08253v1, Appendix A.4, p.32): "In an
nW-equilibrium, for each i = 1,...,n, buyer Bᴷᵢ obtains one of the items χ¹ᵢ or χ̄¹ᵢ, buyer Bᴹᵢ
obtains the other item and both pay V to Sχᵢ."

For every DNF formula `ϕ`, all admissible constants (p.29), every `nW`-equilibrium `o` of `CEx_ϕ`
and every `i`: either `χᵢ` is in the package of `Bᴷᵢ` and `χ̄ᵢ` in that of `Bᴹᵢ`, or the other way
round; and the seller `Sχᵢ` receives at least `2V`.

**Formalization Note.** "χ¹ᵢ, χ̄¹ᵢ" is read as `χᵢ, χ̄ᵢ` (there are no items `χ¹ᵢ`). In (CEx) each
agent has one payment and budget balance is aggregate, so "both pay V to Sχᵢ" is read as the
receipt `q(Sχᵢ) ≥ 2V`, the bound the proof establishes ("If either Bᴷᵢ or Bᴹᵢ would pay less than
V, then either Bχ,1ᵢ or Bχ,2ᵢ could outbid them"). -/
theorem lemma_2 (ϕ : DNF) (T U V W : ℝ) (hA : Admissible ϕ T U V W)
    (o : Outcome (GBuyer ϕ) (GSeller ϕ) (GItem ϕ)) (ho : IsNWEquilibrium ϕ T U V W o)
    (i : Fin ϕ.n) :
    ((Gadget.chi i ∈ o.S (Gadget.BK i) ∧ Gadget.chiBar i ∈ o.S (Gadget.BM i)) ∨
      (Gadget.chiBar i ∈ o.S (Gadget.BK i) ∧ Gadget.chi i ∈ o.S (Gadget.BM i))) ∧
    2 * V ≤ o.q (Gadget.SChi i) := by sorry

end BudgetCoreExchange
