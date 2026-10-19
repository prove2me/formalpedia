-- Prove2me | Theorems.Thm_CrossLicensing_ExPost_proposition_1
-- name    : CrossLicensing.ExPost.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:27:16.742076+00:00
-- url     : https://prove2.me/theorems/be7d3a5c-36d0-48d3-a5d2-6484be4a3118
-- title:
--   Proposition 1, p. 11 — cross-licensing weakly raises supplier profit ex post
-- statement:
--   Fix innovation levels $0\le T_1\le T_2$, effectiveness $0\le\beta\le1$, and a wholesale price $r\ge0$. The manufacturers' quantity game has a Nash equilibrium both with cross-licensing at effectiveness $\beta$ and without it at $\beta=0$. For every equilibrium $q^{\mathrm{cl}}$ of the former game and every equilibrium $q^{\mathrm n}$ of the latter,
--
--   $$
--   r\bigl(q^{\mathrm n}_1+q^{\mathrm n}_2\bigr)\le r\bigl(q^{\mathrm{cl}}_1+q^{\mathrm{cl}}_2\bigr).
--   $$
--
--   This is the supplier's ex-post profit comparison at the same innovation levels and the same wholesale price. **Formalization Note** The weak inequality permits equality, in particular at $\beta=0$. The paper's second sentence interprets this comparison as the final contract choice; it does not specify a separate contract-stage game. Nonnegative $r$ is made explicit because the claim fails at a negative wholesale price.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. 11, Proposition 1; proof p. A.1 (PDF 33)

import Mathlib
import Definitions.Def_CrossLicensing_ExPost_Model

namespace CrossLicensing.ExPost

/-- Proposition 1: cross-licensing weakly increases supplier profit at the same
innovation levels and wholesale price, for every pair of quantity equilibria. -/
theorem proposition_1 (β T₁ T₂ r : ℝ) (h : Standing β T₁ T₂ r) :
    (∃ q, IsQuantityNE β T₁ T₂ r q) ∧
    (∃ q, IsQuantityNE 0 T₁ T₂ r q) ∧
    (∀ qcl qn, IsQuantityNE β T₁ T₂ r qcl → IsQuantityNE 0 T₁ T₂ r qn →
      supplierProfit r qn ≤ supplierProfit r qcl) := by sorry

end CrossLicensing.ExPost
