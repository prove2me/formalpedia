-- Prove2me | Theorems.Thm_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map
-- name    : AdicCompletion.map_ker_subtype_injective_and_range_eq_ker_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/7d1c1e8a-8171-526a-831a-e9eac2ca6f65
-- title:
--   Exactness of I-adic completion on kernels of maps of finite modules
-- statement:
--   Let $R$ be a commutative Noetherian ring, $I \subseteq R$ an ideal, and let $M$, $N$ be $R$-modules that are additive commutative groups with $R$-module structure and are finite (finitely generated) over $R$, all in a single universe $u$; let $\rho : M \to_{R} N$ be an $R$-linear map. Write $\hat{\;\cdot\;}$ for $I$-adic completion, `AdicCompletion I`, and `AdicCompletion.map I` for the functorial action on $R$-linear maps. The theorem asserts the conjunction of two facts about the completion of the inclusion $(\ker \rho).\mathrm{subtype} : \ker \rho \hookrightarrow M$: first, the induced map $\widehat{\ker \rho} \to \hat M$ is injective as a function; second, its range, as a submodule of $\hat M$, coincides exactly with the kernel of the completed map $\hat\rho : \hat M \to \hat N$. Together these say that $I$-adic completion of the inclusion identifies $\widehat{\ker\rho}$ with $\ker(\hat\rho)$; the conclusion is stated as a pair of assertions (injectivity and equality of submodules) rather than as a single isomorphism.
--
--   This is the standard exactness of $I$-adic completion on finitely generated modules over a Noetherian ring (a consequence of the Artin–Rees lemma), packaged in the form needed to identify the completed kernel with the kernel of the completed map. It is used in the construction of presentations of completed modules, namely by [`Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker`](thm.html#Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AdicCompletion.map_ker_subtype_injective_and_range_eq_ker_map
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (ρ : M →ₗ[R] N) :
    Function.Injective (AdicCompletion.map I (LinearMap.ker ρ).subtype) ∧
      LinearMap.range (AdicCompletion.map I (LinearMap.ker ρ).subtype) =
        LinearMap.ker (AdicCompletion.map I ρ) := by sorry
