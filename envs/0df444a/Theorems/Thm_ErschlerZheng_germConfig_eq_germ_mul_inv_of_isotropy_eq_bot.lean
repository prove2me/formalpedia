-- Prove2me | Theorems.Thm_ErschlerZheng_germConfig_eq_germ_mul_inv_of_isotropy_eq_bot
-- name    : ErschlerZheng.germConfig_eq_germ_mul_inv_of_isotropy_eq_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:18.584839+00:00
-- url     : https://prove2.me/theorems/2fb007ef-e6c5-417d-8bdc-2e82cb2b58ba
-- title:
--   (3.3), bundle reading — when L has trivial isotropy at x, Φ_g(x) = (gσ⁻¹, x) for every σ ∈ L with x·σ = x·g, not only for the chosen one
-- statement:
--   Let a group $H$ act from the right by homeomorphisms on a topological space $X$ (`MulAction Hᵐᵒᵖ X`, `ContinuousConstSMul Hᵐᵒᵖ X`), let $L$ be a subgroup of $H$, $g \in H$ and $x \in X$, and suppose the isotropy group of $L$ at $x$ is trivial (`isotropy L x = ⊥`). Then for every $\sigma \in L$ with $x \cdot \sigma = x \cdot g$, the germ configuration $\Phi_g(x)$ (`germConfig L g x`, defined with the chosen element `transport L x (x <• g)` of $L$) equals the germ $(g\sigma^{-1}, x)$ (`germ x (g * σ⁻¹)`).
--
--   This is not a result of the paper. It backs the bundle note `ErschlerZheng_Germs` where it reads `germConfig L g x` as $\Phi_g(x)$ of (3.3) with $\sigma = $ `transport L x (x <• g)`, and where it says that `transport` also supplies the $\sigma$ of (3.3): the paper's “where $\sigma \in L$, $x \cdot g = x \cdot \sigma$” leaves $\sigma$ open, and the statement shows that when $L$ has trivial isotropy at $x$ every such $\sigma$ gives the value of `germConfig`. An auxiliary group with trivial isotropy (`IsAuxiliary`) has trivial isotropy at every point by definition. The statement assumes it only at $x$, and $g$ is any element of $H$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 19, (3.3) does not depend on the choice of σ (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Germs

open scoped RightActions

namespace ErschlerZheng

theorem germConfig_eq_germ_mul_inv_of_isotropy_eq_bot {H : Type*} [Group H] {X : Type*}
    [TopologicalSpace X] [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X] (L : Subgroup H)
    (g : H) (x : X) (hL : isotropy L x = ⊥) (σ : H) (hσ : σ ∈ L) (hσx : x <• σ = x <• g) :
    germConfig L g x = germ x (g * σ⁻¹) := by
  sorry

end ErschlerZheng
