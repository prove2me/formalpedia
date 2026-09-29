-- Prove2me | Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
-- name    : CookPvsNP.npComplete_of_polyReducible
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T13:53:08.611195+00:00
-- url     : https://prove2.me/theorems/c9ac956b-1655-417b-bd21-8eeb85effb5e
-- title:
--   Proposition 1(b): NP-completeness transfers along $\le_p$ into NP
-- statement:
--   Let $\Sigma_1,\Sigma_2$ be finite alphabets, $L_1\subseteq\Sigma_1^*$ and $L_2\subseteq\Sigma_2^*$. If $L_1$ is NP-complete, $L_2\in\mathrm{NP}_{\Sigma_2}$, and $L_1\le_p L_2$, then
--   $$L_2\text{ is NP-complete.}$$
--
--   This is the standard method for proving new problems NP-complete.
-- source:
--   S. Cook, The P versus NP Problem, official Clay Mathematics Institute problem description, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, §2, p. 4, Proposition 1(b)

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- Cook, Proposition 1(b): if `L₁` is NP-complete, `L₂ ∈ NP`, and `L₁ ≤ₚ L₂`, then `L₂` is
NP-complete. -/
theorem npComplete_of_polyReducible {Sym₁ Sym₂ : Type} [Fintype Sym₁] [Fintype Sym₂]
    (L₁ : Lang Sym₁) (L₂ : Lang Sym₂) (h₁ : NPComplete L₁) (h₂ : L₂ ∈ NP Sym₂)
    (h : PolyReducible L₁ L₂) : NPComplete L₂ := by sorry

end CookPvsNP
