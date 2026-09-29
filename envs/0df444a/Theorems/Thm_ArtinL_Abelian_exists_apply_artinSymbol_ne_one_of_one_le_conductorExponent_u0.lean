-- Prove2me | Theorems.Thm_ArtinL_Abelian_exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0
-- name    : ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/b240d5a6-221d-5913-849c-9922b598185f
-- title:
--   Minimality half of the local conductor exponent at v
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a Galois extension whose Galois group $L \simeq_{\mathrm{alg}[K]} L$ is commutative, let $\psi$ be a monoid homomorphism from that Galois group to $\mathbb{C}^\times$, let $v$ be a height-one prime of $\mathcal O_K$, and let $\mathfrak m'$ be an ideal of $\mathcal O_K$ not divisible by $v$. Assume, for some $N \in \mathbb N$, the vanishing hypothesis: for every non-zero $\beta \in \mathcal O_K$ and every ideal $\mathfrak m$ such that the principal fractional ideal $(\beta)$, viewed as a unit of the group of fractional ideals, has valuation $0$ at every prime dividing $\mathfrak m$, if $\beta$ is totally positive (every ring homomorphism $K \to \mathbb R$ sends $\beta$ to a positive real) and $\beta - 1 \in v^N\mathfrak m'$, then $\psi$ of the ray-class Artin symbol $\mathrm{artinSymbol}\,K\,L\,\mathfrak m$ at $(\beta)$ equals $1$. Assume further that the conductor exponent $f = \mathrm{conductorExponent}\,\psi\,v$ — namely $1$ or $0$ according as $\psi$ is non-trivial or trivial on the inertia group at $v$, plus the ceiling of the Swan conductor $\sum_i \frac{\#G_{i+1}}{\#G_0}\cdot[\psi|_{G_{i+1}} \neq 1]$ — satisfies $1 \le f$. Then there exists a non-zero $\alpha \in \mathcal O_K$ with $(\alpha)$ of valuation $0$ at every prime dividing $v\mathfrak m'$, such that $\alpha$ is totally positive, $\alpha - 1 \in v^{\,f-1}\mathfrak m'$, and $\psi\bigl(\mathrm{artinSymbol}\,K\,L\,(v\mathfrak m')\,(\alpha)\bigr) \neq 1$.
--
--   This is the minimality half of the local conductor theorem for an abelian character $\psi$ at a finite place $v$: the exponent computed from the inertia and higher ramification filtration cannot be lowered, since the ray of totally positive elements congruent to $1$ modulo $v^{f-1}\mathfrak m'$ already contains an element on which $\psi$ composed with the Artin symbol is non-trivial. It feeds the comparison of the conductor exponent with the least admissible congruence level used in the Langlands–Tunnell input, being cited by [`ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_conductor_lt_u0`](thm.html#ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_conductor_lt_u0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin
open _root_.NumberField

theorem ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (ψ : (L ≃ₐ[K] L) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (𝔪' : Ideal (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔪')
    (N : ℕ)
    (hN : ∀ (β : 𝓞 K) (hβ : β ≠ 0) (𝔪 : Ideal (𝓞 K)) (hc : principalUnit K β hβ ∈ coprimeToModulus K 𝔪),
      (∀ τ : K →+* ℝ, 0 < τ (β : K)) → β - 1 ∈ v.asIdeal ^ N * 𝔪' →
        ψ (artinSymbol K L 𝔪 ⟨principalUnit K β hβ, hc⟩) = 1)
    (hf : 1 ≤ ArtinL.Abelian.conductorExponent ψ v) :
    ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K (v.asIdeal * 𝔪')),
      (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧ α - 1 ∈ v.asIdeal ^ (ArtinL.Abelian.conductorExponent ψ v - 1) * 𝔪' ∧
        ψ (artinSymbol K L (v.asIdeal * 𝔪') ⟨principalUnit K α hα, hc⟩) ≠ 1 := by sorry
