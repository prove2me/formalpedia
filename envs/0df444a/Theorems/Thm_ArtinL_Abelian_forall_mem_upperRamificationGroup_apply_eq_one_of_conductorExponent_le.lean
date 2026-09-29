-- Prove2me | Theorems.Thm_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le
-- name    : ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/df2bddb4-a2d1-5d39-92f5-81715e267aed
-- title:
--   Characters kill upper ramification groups above the conductor exponent
-- statement:
--   Let $K$ and $M$ be number fields with $M$ an extension of $K$ that is Galois, let $\psi \colon (M \simeq_{\mathrm{alg}[K]} M) \to \mathbb{C}^{\times}$ be a homomorphism of the Galois group into the units of $\mathbb{C}$, let $v$ be a height-one prime of $\mathcal{O}_K$, and let $n$ be a natural number with $\mathrm{conductorExponent}\,\psi\,v \le n$; here the conductor exponent is $\varepsilon + \lceil \mathrm{Swan}(\psi,v)\rceil$ rounded up in $\mathbb{N}$, where $\varepsilon = 0$ if $\psi$ is trivial on `inertiaGroup K M v` and $\varepsilon = 1$ otherwise, and the Swan conductor is the finite sum over $i \in \mathbb{N}$ of $\bigl(\#\,\mathrm{ramificationGroup}\,K\,M\,v\,(i+1)\bigr)/\bigl(\#\,\mathrm{inertiaGroup}\,K\,M\,v\bigr)$ times the indicator of the condition that $\psi$ is non-trivial on the $(i+1)$-st ramification group. Let $A$ be the valuation subring of $M$ attached to the valuation of the chosen nonzero prime [`LanglandsTunnell.P2.Artin.primeAbove K M v`](def/LanglandsTunnell_ArtinFrobenius.html#L40) of $\mathcal{O}_M$ above $v$. The conclusion is that every $\sigma$ in the upper ramification group of $A$ over $K$ at level $n$, viewed as a rational number — that is, in the lower ramification group of index $\inf\{m : n \le \varphi(m)\}$, the inertia subgroup of the $(m+1)$-st power of the maximal ideal inside the decomposition subgroup of $A$ over $K$ — satisfies $\psi(\sigma) = 1$ for the underlying $K$-automorphism of $M$.
--
--   This is the standard compatibility between the conductor exponent of a one-dimensional Artin character and the filtration by upper (Herbrand-renumbered) ramification groups: a character is trivial on $G^{u}$ as soon as $u$ reaches its conductor exponent. It is what allows the Artin map to be shown trivial on the ray modulo $v^{n}$, and it is used in the computation of the Artin symbol on principal units and in the verification that the local components of the cubic character of the Langlands–Tunnell argument are trivial on sufficiently deep higher unit groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

theorem ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : ArtinL.Abelian.conductorExponent ψ v ≤ n) :
    ∀ σ ∈ ValuationSubring.upperRamificationGroup K (((⟨LanglandsTunnell.P2.Artin.primeAbove K M v, inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K M v⟩ :
          HeightOneSpectrum (𝓞 M)).valuation M).valuationSubring) (n : ℚ),
      ψ ((σ : ↥((((⟨LanglandsTunnell.P2.Artin.primeAbove K M v, inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K M v⟩ :
          HeightOneSpectrum (𝓞 M)).valuation M).valuationSubring).decompositionSubgroup K)) : M ≃ₐ[K] M) = 1 := by sorry
