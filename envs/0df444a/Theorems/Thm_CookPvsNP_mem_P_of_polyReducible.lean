-- Prove2me | Theorems.Thm_CookPvsNP_mem_P_of_polyReducible
-- name    : CookPvsNP.mem_P_of_polyReducible
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T13:50:21.397486+00:00
-- url     : https://prove2.me/theorems/8b828ca9-3b9e-4e57-a4a7-4177a34db56b
-- title:
--   Proposition 1(a): $L_1\le_p L_2$ and $L_2\in$ P imply $L_1\in$ P
-- statement:
--   Let $\Sigma_1,\Sigma_2$ be finite alphabets, $L_1\subseteq\Sigma_1^*$ and $L_2\subseteq\Sigma_2^*$. If $L_1\le_p L_2$ and $L_2\in\mathrm P_{\Sigma_2}$, then
--   $$L_1\in\mathrm P_{\Sigma_1}.$$
--
--   Here $L_1\le_p L_2$ means that some polynomial-time computable $f:\Sigma_1^*\to\Sigma_2^*$ satisfies $x\in L_1\iff f(x)\in L_2$ for all $x$ (Definition 3).
-- source:
--   S. Cook, The P versus NP Problem, official Clay Mathematics Institute problem description, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, §2, p. 4, Proposition 1(a)

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- Cook, Proposition 1(a): if `L₁ ≤ₚ L₂` and `L₂ ∈ P`, then `L₁ ∈ P`. -/
theorem mem_P_of_polyReducible {Sym₁ Sym₂ : Type} [Fintype Sym₁] [Fintype Sym₂]
    (L₁ : Lang Sym₁) (L₂ : Lang Sym₂) (h : PolyReducible L₁ L₂) (h₂ : L₂ ∈ P Sym₂) :
    L₁ ∈ P Sym₁ := by sorry

end CookPvsNP
