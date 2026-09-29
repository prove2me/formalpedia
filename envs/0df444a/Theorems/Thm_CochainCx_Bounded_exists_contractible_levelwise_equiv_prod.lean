-- Prove2me | Theorems.Thm_CochainCx_Bounded_exists_contractible_levelwise_equiv_prod
-- name    : CochainCx.Bounded.exists_contractible_levelwise_equiv_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/01c36baf-f5aa-5984-a3ca-05584153a15c
-- title:
--   Levelwise splitting of a bounded complex over a field
-- statement:
--   Let $k$ be a field and let $C$ be a bounded $\mathbb N$-indexed cochain complex of $k$-vector spaces, i.e. a family of $k$-modules $C^p =$ `C.X p` ($p \in \mathbb N$) with $k$-linear differentials $d_p \colon C^p \to C^{p+1}$ satisfying $d_{p+1} \circ d_p = 0$, together with a bound $N$ such that $C^n$ is a subsingleton for all $n \ge N$. The assertion is that there exist a further bounded complex $E$ of the same shape, a family of $k$-linear maps $\sigma_p \colon E^{p+1} \to E^p$ such that $\sigma_0(d_0 x) = x$ for every $x \in E^0$ and $\sigma_{p+1}(d_{p+1} x) + d_p(\sigma_p x) = x$ for every $p$ and every $x \in E^{p+1}$ (so $\sigma$ is a contracting homotopy exhibiting the identity of $E$ as null-homotopic), and a family of $k$-linear isomorphisms $e_p \colon C^p \;\xrightarrow{\ \sim\ }\; \mathrm{C.H}\, p \times E^p$, where `C.H p` denotes the space attached to $C$ in degree $p$ playing the role of its cohomology, such that for all $p$ and all $x \in C^p$ one has $e_{p+1}(d_p x) = \bigl(0,\; d^E_p((e_p x)_2)\bigr)$. Thus under $e$ the differential of $C$ becomes the direct sum of the zero differential on the `C.H`-components and the differential of $E$; no compatibility beyond this single identity is asserted.
--
--   This is the classical splitting, available over a field, of a complex of vector spaces as the direct sum of its cohomology equipped with the zero differential and a complex with a contracting homotopy. It is used in the dimension count [`CochainCx.Bounded.finrank_HTot_tensor_eq_sum_mul`](thm.html#CochainCx.Bounded.finrank_HTot_tensor_eq_sum_mul), where the splitting reduces a Künneth-type computation for a tensor product of bounded complexes to the contractible summands.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CochainCx_Bounded_exists_contractible_levelwise_equiv_prod.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CochainCx.Bounded.exists_contractible_levelwise_equiv_prod
    {k : Type u} [Field k] (C : CochainCx.Bounded k) :
    ∃ (E : CochainCx.Bounded k) (σ : ∀ p : ℕ, E.X (p + 1) →ₗ[k] E.X p)
      (_ : ∀ x : E.X 0, σ 0 (E.d 0 x) = x)
      (_ : ∀ (p : ℕ) (x : E.X (p + 1)), σ (p + 1) (E.d (p + 1) x) + E.d p (σ p x) = x)
      (e : ∀ p : ℕ, C.X p ≃ₗ[k] (C.H p × E.X p)),
      ∀ (p : ℕ) (x : C.X p), e (p + 1) (C.d p x) = (0, E.d p (e p x).2) := by sorry
