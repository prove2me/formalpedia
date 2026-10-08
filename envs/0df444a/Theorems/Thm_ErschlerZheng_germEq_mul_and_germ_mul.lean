-- Prove2me | Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
-- name    : ErschlerZheng.germEq_mul_and_germ_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-05T23:04:12.691886+00:00
-- url     : https://prove2.me/theorems/61ba0498-583b-4398-af7e-80c8547e1b76
-- title:
--   pp. 17, 52 — the composition of germs (g, x)(h, x·g) = (gh, x) is well defined, and the germ map is multiplicative on the stabilizer
-- statement:
--   Let a group $H$ act from the right on a topological space $X$, each map $y \mapsto y \cdot h$ continuous, and let $x \in X$. Then:
--
--   1. for all $g_1, g_2, h_1, h_2 \in H$: if $g_1$ and $g_2$ agree on a neighbourhood of $x$ (`GermEq x g₁ g₂`) and $h_1$ and $h_2$ agree on a neighbourhood of $x \cdot g_1$, then $g_1h_1$ and $g_2h_2$ agree on a neighbourhood of $x$;
--   2. for $g, h$ fixing $x$, the germ of $gh$ at $x$ is the product of the germs: `germ x (g * h) = germ x g * germ x h` in the germ group at $x$.
--
--   Erschler and Zheng, p. 17: “two germs $(g_1, x_1)$ and $(g_2, x_2)$ are equal if $x_1 = x_2$ and $g_1, g_2$ coincide on a neighborhood of $x_1$. A composition $(g_1, x_1)(g_2, x_2)$ is defined if and only if $x_1 \cdot g_1 = x_2$.” and p. 52: “Recall the multiplication rule in the groupoid of germs: $(\boldsymbol\gamma^{\boldsymbol\epsilon}, x) = (\gamma_n^{\epsilon_n}, x)(\gamma_{n-1}^{\epsilon_{n-1}}, x \cdot \gamma_n^{\epsilon_n}) \ldots (\gamma_1^{\epsilon_1}, x \cdot \gamma_n^{\epsilon_n} \ldots \gamma_2^{\epsilon_2})$.”
--
--   The rule is $(g, x)(h, x \cdot g) = (gh, x)$. The first conjunct says that it does not depend on the elements chosen to represent the two germs; the second, that on the elements fixing $x$ it is the group law of `GermGroup x`. The proof of Fact 3.5 (p. 19) uses the same rule.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 17, the germ cocycle, also pp. 19 and 52

import Mathlib
import Definitions.Def_ErschlerZheng_Germs
open scoped RightActions

namespace ErschlerZheng

theorem germEq_mul_and_germ_mul {H : Type*} [Group H] {X : Type*} [TopologicalSpace X]
    [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X] (x : X) :
    (∀ g₁ g₂ h₁ h₂ : H, GermEq x g₁ g₂ → GermEq (x <• g₁) h₁ h₂ →
        GermEq x (g₁ * h₁) (g₂ * h₂)) ∧
      ∀ g h : H, x <• g = x → x <• h = x → germ x (g * h) = germ x g * germ x h := by
  sorry

end ErschlerZheng
