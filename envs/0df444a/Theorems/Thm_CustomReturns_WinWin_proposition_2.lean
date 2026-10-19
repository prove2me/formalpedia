-- Prove2me | Theorems.Thm_CustomReturns_WinWin_proposition_2
-- name    : CustomReturns.WinWin.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:07.479137+00:00
-- url     : https://prove2.me/theorems/95997a00-fc21-4bc7-aa25-1239138a9989
-- title:
--   Proposition 2: allowing customized returns can increase profit and reduce total returns
-- statement:
--   There are parameters satisfying the paper's model assumptions for which the firm has an optimal nonnegative price-and-fee policy with positive customized-product returns. At every optimal policy for those parameters, disallowing customized-product returns while keeping the standard-product terms fixed has an optimum, and every such counterfactual optimum has strictly smaller profit and strictly more total returns:
--
--   $$
--   R_c^*>0,\qquad
--   \Pi_{\mathrm{no\ }c\mathrm{\ returns}}^*<\Pi^*,\qquad
--   R_{\mathrm{tot}}^*<R_{\mathrm{tot,no\ }c\mathrm{\ returns}}^*.
--   $$
--
--   This formalizes the paper's claim that a customized-product return option can benefit the firm while reducing its overall return volume.
--
--   **Formalization Note** Both original and counterfactual optima are asserted to exist, and the inequalities hold for every optimum, so the claim cannot be satisfied by an empty choice set or arbitrary named policies. The counterfactual follows problem (5): it holds the standard terms of the original optimal policy fixed and reoptimizes customized terms subject to $R_c=0$.
-- source:
--   Esenduran, Letizia & Ovchinnikov, Customization and Returns, accepted manuscript (Management Science, accepted Dec. 13, 2021; SSRN 3444244), p. 11 (PDF 11), Proposition 2; counterfactual in proof of Proposition 2, Online Appendix pp. 14–15 (PDF 30–31), problems (4)–(5)

import Mathlib
import Definitions.Def_CustomReturns_WinWin_Model

namespace CustomReturns.WinWin

/-- Proposition 2, p. 11: there are model parameters at which permitting
customized-product returns strictly increases profit and strictly reduces
the firm's total returns relative to problem (5). -/
theorem proposition_2 :
    ∃ P : Params, P.Standing ∧ (∃ x : Policy, IsOptimal P x) ∧
      ∀ x : Policy, IsOptimal P x →
        0 < RC P x ∧
        (∃ y : Policy, IsOptimalNoCReturns P x y) ∧
        ∀ y : Policy, IsOptimalNoCReturns P x y →
          profit P y < profit P x ∧ totalReturns P x < totalReturns P y := by sorry

end CustomReturns.WinWin
