-- Prove2me | Theorems.Thm_CoRSuccGap_Supplement_theorem_1_4
-- name    : CoRSuccGap.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:41:16.499856+00:00
-- url     : https://prove2.me/theorems/d968401d-1c31-4d2a-a0c5-77b9665a8258
-- title:
--   Theorem 1.4 -- exponential quantifier lower bound from $FO^3$ to $FO^2$
-- statement:
--   Let $k\ge1$. Every unrestricted $FO^2$ formula whose binary assignment relation agrees with $G_k$ on every finite nonempty structure has at least
--
--   $$
--   2^k
--   $$
--
--   existential or universal quantifier occurrences. The count is total occurrences, not quantifier depth, relation atoms or total syntax nodes.
--
--   This is the exact lower bound: the paper's displayed $FO^2$ expansion uses $2^k$ quantifiers.
--
--   Differences from the source:
--   - generalization: $\varphi\equiv G_k$ means agreement on every nonempty structure → Lean assumes agreement only on every finite nonempty structure; reason: the paper explicitly states that its proof gives this stronger finite-structure form on p.33.
-- source:
--   Uezato--Nakamura, arXiv:2609.26778 (held version, sha256 5ad6337d...), Theorem 1.4, p.32 (PDF 34), finite-structure strengthening p.33 (PDF 35)

import Definitions.Def_CoRSuccGap_Gk
import Definitions.Def_CoRSuccGap_Supplement_FiniteVariableLogic

set_option autoImplicit false

namespace CoRSuccGap
namespace Supplement

/-- **Theorem 1.4 (Exponential lower bound from FO³ to FO²).** Uezato--Nakamura,
*An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations*,
arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Theorem 1.4, p.32 (PDF 34).

For every `k ≥ 1`, an unrestricted FO² formula over `P₁,…,Pₖ,Q₁,…,Qₖ` whose binary
assignment relation agrees with `G_k` on every finite nonempty structure contains at least `2^k`
existential or universal quantifier occurrences. -/
theorem theorem_1_4 (k : ℕ) (hk : 1 ≤ k) (p : FOFormula (GSym k) (Fin 2))
    (hagree : ∀ (D : Type) [Fintype D] [Nonempty D]
      (M : GSym k → D → D → Prop), p.query2 M = Gk k M) :
    2 ^ k ≤ p.numQuantifiers := by sorry

end Supplement
end CoRSuccGap
