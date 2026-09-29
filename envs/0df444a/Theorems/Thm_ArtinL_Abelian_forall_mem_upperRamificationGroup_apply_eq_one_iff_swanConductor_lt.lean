-- Prove2me | Theorems.Thm_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt
-- name    : ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/0cea2164-9081-5bbf-8392-f94de04cba83
-- title:
--   Upper ramification jumps versus Swan conductor of ψ
-- statement:
--   Let $K$ and $M$ be number fields with $M/K$ Galois, let $\psi\colon (M \simeq_{\mathrm{alg}[K]} M) \to \mathbb{C}^\times$ be a multiplicative homomorphism from $\mathrm{Gal}(M/K)$ to $\mathbb{C}^\times$, and let $v$ be a height-one prime of $\mathcal{O}_K$. Write $\mathfrak{P} =$ [`LanglandsTunnell.P2.Artin.primeAbove K M v`](def/LanglandsTunnell_ArtinFrobenius.html#L40) for the chosen prime of $\mathcal{O}_M$ above $v$, which is nonzero, and set $G_i = (\mathfrak{P}^{i+1}).\mathrm{inertia}$ inside $\mathrm{Gal}(M/K)$, so that $G_0$ is the inertia subgroup at $\mathfrak{P}$. Assume $\psi$ is ramified at $v$, i.e. it is not the case that $\psi(\sigma) = 1$ for all $\sigma \in G_0$, and let $u \in \mathbb{Q}$ with $0 \le u$. Let $A \subseteq M$ be the valuation subring of the $\mathfrak{P}$-adic valuation on $M$, with decomposition subgroup $D = A.\mathrm{decompositionSubgroup}\,K$, and let $G^u \le D$ be the upper-numbering ramification group, defined as the lower ramification group $((\mathfrak{m}_A)^{n+1}).\mathrm{inertia}\,D$ for $n$ the least natural number with $u \le \varphi(n)$ (Herbrand's function). The conclusion is the equivalence: $\psi$ is trivial on the image of $G^u$ in $\mathrm{Gal}(M/K)$ if and only if $$\sum_{i \ge 0} \frac{\#G_{i+1}}{\#G_0}\cdot[\,\psi|_{G_{i+1}} \ne 1\,] < u,$$ the locally finite sum defining [`ArtinL.Abelian.swanConductor`](def/ArtinL_Abelian.html#L49).
--
--   This identifies, for a ramified abelian Artin character, the set of upper-numbering levels killed by the character as the rationals strictly above its Swan conductor; equivalently the last upper jump of $\psi$ at $v$ is $\mathrm{Swan}(\psi, v)$, with no integrality (Hasse–Arf) assertion. It is used to produce, from a conductor exponent at least $1$, a decomposition-group element on which the character is nontrivial, in [`ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0`](thm.html#ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

theorem ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (hram : ¬ ArtinL.Abelian.IsUnramifiedAt ψ v) (u : ℚ) (hu : 0 ≤ u) :
    (∀ σ ∈ ValuationSubring.upperRamificationGroup K (((⟨LanglandsTunnell.P2.Artin.primeAbove K M v, inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K M v⟩ :
          HeightOneSpectrum (𝓞 M)).valuation M).valuationSubring) u,
        ψ ((σ : ↥((((⟨LanglandsTunnell.P2.Artin.primeAbove K M v, inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K M v⟩ :
          HeightOneSpectrum (𝓞 M)).valuation M).valuationSubring).decompositionSubgroup K)) : M ≃ₐ[K] M) = 1) ↔
      ArtinL.Abelian.swanConductor ψ v < u := by sorry
