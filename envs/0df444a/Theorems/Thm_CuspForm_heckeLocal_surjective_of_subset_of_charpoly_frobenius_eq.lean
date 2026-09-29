-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_surjective_of_subset_of_charpoly_frobenius_eq
-- name    : CuspForm.heckeLocal.surjective_of_subset_of_charpoly_frobenius_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/b1e71c51-dcff-5e17-9f54-9cd1985e6e11
-- title:
--   Surjectivity of the Hecke comparison map for S₁ ⊆ S
-- statement:
--   Let $\mathcal{O}$ be a complete discrete valuation domain of characteristic zero with finite residue field $k = \mathrm{ResidueField}\,\mathcal{O}$, let $p$ be a prime lying in the maximal ideal of $\mathcal{O}$, and let $\bar\rho$ be a residual Galois representation over $k$, i.e. a two-dimensional $k$-vector space with a monoid homomorphism from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to its endomorphisms that is trivial on the fixing group of some finite subextension, assumed absolutely irreducible (irreducible after base change to $\overline{k}$). Let $S_1 \subseteq S$ be finite sets of naturals with $p \in S_1$, and $N \neq 0$ with every prime divisor of $N$ in $S_1$; assume the weight-two cusp forms on $\Gamma_0(N)$ are $\mathbb{C}$-spanned by those with integral $q$-coefficients. Let $\theta_1$ be a ring homomorphism to $k$ from the $\mathbb{Z}$-algebra generated inside $\mathrm{End}_{\mathbb{C}}$ by the operators $T_\ell$ ($\ell$ prime, $\ell \nmid N$, $\ell \notin S_1$) and $U_q$ ($q$ prime, $q \mid N$, $q \notin S_1$), such that for each prime $\ell \nmid N$ with $\ell \notin S_1$, each valuation subring $P$ of $\overline{\mathbb{Q}}$ in which $\ell$ is a non-unit, and each $\sigma$ acting on the residue field of $P$ as $x \mapsto x^{\ell}$ from the decomposition group, the characteristic polynomial of $\bar\rho(\sigma)$ equals $X^2 - \theta_1(T_\ell)X + \ell$. Let $\theta$ be the composite of $\theta_1$ with the inclusion of the algebra for $S$ into that for $S_1$, and let $\Psi$ be an $\mathcal{O}$-algebra homomorphism between the corresponding localisations $\mathbb{T}_\theta \to \mathbb{T}_{\theta_1}$ commuting with the structure maps $\pi$. Then $\Psi$ is surjective.
--
--   This is the statement that at an absolutely irreducible (non-Eisenstein) residual character the local anemic Hecke algebra does not depend on which finite set of good primes is omitted: the comparison map for a larger omitted set is onto, as in Lemma 3.27(b) of Darmon–Diamond–Taylor. It feeds the bijectivity statement for such comparison maps, the identification of the images of the operators $T_\ell$, and the freeness/base-change statements used in the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_surjective_of_subset_of_charpoly_frobenius_eq.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.heckeLocal.surjective_of_subset_of_charpoly_frobenius_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S S₁ : Finset ℕ) (hpS₁ : p ∈ S₁) (hS₁ : S₁ ⊆ S)
    (N : ℕ) [NeZero N] (hNS₁ : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S₁)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₁ : CuspForm.heckeAlgebra N 2 (↑S₁ : Set ℕ) →+* ResidueField 𝒪)
    (hθ₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS₁ : ℓ ∉ (↑S₁ : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS₁)) * X + C (ℓ : ResidueField 𝒪))

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
      θ t = θ₁ (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₁)) t))
    (Ψ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] CuspForm.heckeLocal N (↑S₁ : Set ℕ) 𝒪 θ₁)
    (hΨ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
      Ψ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ t) =
        CuspForm.heckeLocal.π N (↑S₁ : Set ℕ) 𝒪 θ₁
          (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₁)) t)) :
    Function.Surjective Ψ := by sorry
