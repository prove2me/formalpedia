-- Prove2me | Theorems.Thm_AutomorphicForm_mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm
-- name    : AutomorphicForm.mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/9505b69b-9129-5262-b2b2-a61252eb4906
-- title:
--   Central translates that are twisted norms yield idelic norms
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$, and let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$, so that $\mathrm{Gal}(L/K)$ is cyclic with generator $\sigma$. Let $a,b$ be units of $K$ with $a \neq b$, and assume that $a$, viewed in $K$, lies in the image of the norm map $\mathrm{Algebra.norm}\,K : L \to K$. Let $z$ be an idele of $K$, i.e. a unit of $\mathrm{AdeleRing}\,(\mathcal{O}_K)\,K$. Form the element $\gamma \in \mathrm{GL}_2(\mathbb{A}_K)$ given by the product of the scalar matrix with diagonal entry $z$ ([`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18)) and the image under the adelic entrywise map [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) of the diagonal matrix $\mathrm{diag}(a,b) \in \mathrm{GL}_2(K)$ (`diagUnits2`), so $\gamma = \mathrm{diag}(za,zb)$. Assume $\gamma$ satisfies [`AutomorphicForm.IsNormOf`](def/AutomorphicForm_TwistedOrbital.html#L217) relative to $\sigma$ for some $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$: there exist $\delta$ and $y \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ with the image of $\gamma$ under `toTensorGL` equal to $y^{-1} \cdot \mathrm{normString}\,K\,L\,\mathbb{A}_K\,\sigma\,\delta \cdot y$. Then $z$ lies in the range of the idelic norm attached to the base change `genuineBaseChange K L`, that is, of the map on ideles induced by $\mathrm{Algebra.norm}\,\mathbb{A}_K : \mathbb{A}_L \to \mathbb{A}_K$ taken along the ring homomorphism $\mathbb{A}_K \to \mathbb{A}_L$.
--
--   This is the norm-support condition in the comparison of hyperbolic terms for cyclic base change for $\mathrm{GL}(2)$: a regular split rational element scaled by a central idele can be a twisted norm only if that idele is itself an idelic norm from $L$. It feeds the statement that the $K$-side integrand of a normic class vanishes off the image of the idelic norm, and is used in the slope-transfer identity for hyperbolic contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a b : Kˣ) (hab : a ≠ b)
    (ha : (a : K) ∈ Set.range (Algebra.norm K : L → K))
    (z : (AdeleRing (𝓞 K) K)ˣ)
    (h : ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ
        (AutomorphicForm.centralScalar (𝓞 K) K z * AutomorphicForm.globalPoints (𝓞 K) K (diagUnits2 a b)) δ) :
    z ∈ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm := by sorry
