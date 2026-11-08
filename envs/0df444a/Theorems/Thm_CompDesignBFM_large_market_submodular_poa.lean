-- Prove2me | Theorems.Thm_CompDesignBFM_large_market_submodular_poa
-- name    : CompDesignBFM.large_market_submodular_poa
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:25.776992+00:00
-- url     : https://prove2.me/theorems/1a5fc5f2-6230-4f06-8b7e-891207447c68
-- title:
--   §1.2.2 — monotone submodular: an equilibrium exists and OPT ≤ (1 + 1/(1 − l)) v(S)
-- statement:
--   Let $v$ be normalized, monotone and submodular, $B>0$, $c\ge0$, and suppose $c_i\le lB$ for all $i$, where $0\le l<1$. Then the marginal-contribution game has a pure Nash equilibrium, and every pure Nash equilibrium $S$ satisfies
--
--   $$\mathrm{OPT}\le\Bigl(1+\frac1{1-l}\Bigr)v(S),$$
--
--   so the price of anarchy is at most $2+o_\lambda(1)$. This is the source of the limit 2 in the large-market clause of the goal.
--
--   Differences from the source:
--   - generalization: price of anarchy at most 2 + o_λ(1) → the explicit bound OPT ≤ (1 + 1/(1 − l)) v(S); reason: an explicit rate, tending to 2 as l → 0, which implies the printed asymptotic form
--   - encoding: PoA as a ratio, infinite at a zero denominator (p.5) → OPT ≤ ρ · v(S) for every equilibrium S; reason: no ratio is formed, so no convention at zero is needed
--   - encoding: λ = max_i c_i/B → any l with 0 ≤ l < 1 and c_i ≤ l·B for all i; reason: λ is the least such l; 0 ≤ l follows from c ≥ 0 whenever n ≥ 1, and at n = 0 the claim is trivial
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1.2.2, p.6 (PDF 8)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_OPT

namespace CompDesignBFM

/-- §1.2.2 opening, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.6, PDF 8. For monotone submodular valuations, the marginal-contribution game admits a
pure Nash equilibrium and has price of anarchy at most `2 + o_λ(1)`, in the explicit form: if `cᵢ ≤ l B` for all
`i` with `0 ≤ l < 1`, then every pure Nash equilibrium `S` has `OPT ≤ (1 + 1 / (1 - l)) v(S)`.
**Formalization Note.** A price of anarchy bound `ρ` is written `OPT ≤ ρ v(S)` for each equilibrium `S`, with no
ratio and so no convention at a zero denominator. -/
theorem large_market_submodular_poa {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) (hcl : ∀ i, c i ≤ l * B) :
    (∃ S : Finset (Fin n), IsPNE v B c S) ∧
      ∀ S : Finset (Fin n), IsPNE v B c S → OPT v B c ≤ (1 + 1 / (1 - l)) * v S := by sorry

end CompDesignBFM
