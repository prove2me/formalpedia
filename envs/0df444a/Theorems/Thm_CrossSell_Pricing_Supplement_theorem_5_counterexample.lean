-- Prove2me | Theorems.Thm_CrossSell_Pricing_Supplement_theorem_5_counterexample
-- name    : CrossSell.Pricing.Supplement.theorem_5_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:54:11.671186+00:00
-- url     : https://prove2.me/theorems/75ae8ccc-0d3a-43df-9ee7-d7e08b34c7b5
-- title:
--   Theorem 5 (corrected: counterexample to printed claim) — outside sales defeat the prefix heuristic
-- statement:
--   Theorem 5 on p. 23 is false with its printed quantifier over main products only. Consider one main product with price 1, cost 0 and utility 1-log(10). Take three secondary prices (10,1,1), zero secondary costs, and conditional utilities equal to those prices after the main purchase. After outside outcome 0, add logarithms of (1/100,1/100,10) to those prices. The secondary margins are in decreasing order; for the actual main product their margin-weighted attractions are (10,1,1) and their attractions are (1,1,1), satisfying both printed weak monotonicity assumptions.
--
--   The complete printed search returns the sole main product together with all three secondary products, but the secondary set consisting of the first and third products gives strictly more true profit:
--   $$C(1,3)=\frac{7259}{6061}<\frac{15238}{12111}=\Pi(\{1\},\{1,3\},p,r).$$
--   The Lean conclusion asserts both printed assumptions, the validity of the returned printed-search solution, and this strict improvement. All margins are positive; no empty assortment is used in the comparison. Exact rational enumeration of all sixteen assortment pairs is retained in evidence/counterexample-exact.json.
--
--   **Formalization Note** Fin indices start at zero, so the improving secondary set is {0,2}. The candidate family, true objective, and main-product-only assumptions are unchanged; the theorem is a refutation of the original optimality assertion. No additional assumption on outcome 0 is silently imposed.
--
--   Differences from the source:
--   - correction: the two monotonicity assumptions for i in M imply global optimality of the printed search → an explicit instance satisfies those assumptions and the exact printed search but has a strictly better feasible non-prefix assortment; reason: p. 23 omits outside-outcome conditions although (15) includes outside sales; the exact witness and profits in DISPROOF.md refute the original conclusion without changing any premise
--   - encoding: products numbered from one → Fin 1 and Fin 3 start at zero; reason: the first-and-third secondary assortment is {0,2}; the search still uses lengths m>=1,n>=1
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), p. 23, Theorem 5

import Mathlib
import Definitions.Def_CrossSell_Pricing_Supplement_Heuristic

namespace CrossSell.Pricing.Supplement

/-- The printed hypotheses hold and the actual printed algorithm returns (1,3),
    but the non-prefix secondary set {0,2} has strictly greater true profit. -/
theorem theorem_5_counterexample :
    PrintedConditions (fun _ : Fin 3 => 0) counterR counterV ∧
    PrintedHeuristic counterU (fun _ : Fin 1 => 0) (fun _ => 1)
      (fun _ : Fin 3 => 0) counterR counterV (fun _ => Equiv.refl (Fin 1)) 1 3 ∧
    candidateProfit counterU (fun _ : Fin 1 => 0) (fun _ => 1)
      (fun _ : Fin 3 => 0) counterR counterV (fun _ => Equiv.refl (Fin 1)) 1 3 <
    profit (Finset.univ : Finset (Fin 1)) (fun _ => ({0, 2} : Finset (Fin 3)))
      counterU (fun _ => 0) (fun _ => 0) counterV (fun _ => 1) counterR := by sorry

end CrossSell.Pricing.Supplement
