-- Prove2me | Theorems.Thm_CohCarrier_exists_charInvolution_cornerSubmodule_H1_linearEquiv_eigenspace_map_mkQ_of_isAbsolutelyIrreducible
-- name    : CohCarrier.exists_charInvolution_cornerSubmodule_H1_linearEquiv_eigenspace_map_mkQ_of_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/19e7a58b-ee97-5b09-80b1-800ba192a70d
-- title:
--   Balanced ±1 eigenspaces of the conjugation involution on a corner of H¹
-- statement:
--   Let $\mathcal{O}$ be a characteristic-zero discrete valuation domain, $k$ a field which is an $\mathcal{O}$-algebra with $\mathcal{O}\to k$ surjective, $p\neq 2$ a prime with $\operatorname{char}k=p$, $M'\geq 1$, $H'\leq(\mathbb{Z}/M')^\times$ a subgroup and $S$ a finite set of naturals. Let $\mathbb{T}$ be a commutative $\mathcal{O}$-algebra acting on $H^1=\operatorname{Hom}(\Gamma_{H'}(M'),\mathcal{O})$ (additive homomorphisms from the group $\Gamma_{H'}(M')$ written additively), compatibly with the $\mathcal{O}$-action and faithfully (any $t$ killing all of $H^1$ is $0$), and let $op$ assign to each formal generator $T_\ell$ ($\ell$ prime, $\ell\notin S$, $\ell\nmid M'$), $U_q$ ($q$ prime, $q\mid M'$) and $\langle d\rangle$ ($d\in(\mathbb{Z}/M')^\times$) an element of $\mathbb{T}$ acting as the corresponding member of [`CohCarrier.opFamily`](def/CohCarrier_Inst.html#L91) (transfer of the pull-back along conjugation by $\mathrm{diag}(1,\ell)$, resp. the diamond operator), the range of $op$ generating $\mathbb{T}$ over $\mathcal{O}$. Let $S'$ be a family of complete orthogonal idempotents $e_i$ of $\mathbb{T}$ together with maximal ideals $\mathfrak{m}_i$ exhausting all maximal ideals, with $e_i\in\mathfrak{m}_j$ exactly when $i\neq j$, fix $i_0$, put $A=e_{i_0}\mathbb{T}e_{i_0}$, and let $\pi\colon A\to k$ be an $\mathcal{O}$-algebra map with $\pi(e_{i_0}\,op(g)\,e_{i_0})=\bar\theta(g)$ for a given family $\bar\theta$ of values in $k$. Assume given $\bar\rho$, a two-dimensional $k$-representation of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ factoring through a finite level, absolutely irreducible (irreducible after base change to $\overline{k}$), with $\operatorname{tr}\bar\rho(\sigma)=\bar\theta(T_\ell)$ for every prime $\ell\notin S$ with $\ell\nmid M'$, every valuation subring $A'$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A'$, and every $\sigma$ that is a Frobenius at $\ell$ for $A'$. Then there is an $A$-linear endomorphism $\tau$ of the corner module $P=e_{i_0}\cdot H^1$ given on elements by the involution $\varphi\mapsto\varphi\circ \mathrm{jConj}$ of $H^1$ (pull-back along the conjugation involution of $\Gamma_{H'}(M')$), such that the images of $\ker(\tau-1)$ and of $\ker(\tau+1)$ in the fibre $P/\mathfrak{m}_A P$ are isomorphic as $A$-modules.
--
--   This is the assertion, used by Wiles in the proof of his Theorem 2.1, that complex conjugation has as many $+1$ as $-1$ eigenvalues on the relevant fibre of a local factor of the weight-two cohomology of $\Gamma_{H'}(M')$, here in the shape of an abstract isomorphism between the images of the two eigenkernels in $P/\mathfrak{m}P$. It feeds the statement that the corner module is spanned by the Hecke translates of a pair of elements, one from each eigenspace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_charInvolution_cornerSubmodule_H1_linearEquiv_eigenspace_map_mkQ_of_isAbsolutelyIrreducible.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_charInvolution_cornerSubmodule_H1_linearEquiv_eigenspace_map_mkQ_of_isAbsolutelyIrreducible
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ) (S : Finset ℕ)
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (CohCarrier.H1 M' H' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (CohCarrier.H1 M' H' 𝒪)]
    (hfaith : ∀ t : 𝕋, (∀ v : CohCarrier.H1 M' H' 𝒪, t • v = 0) → t = 0)
    (op : CohCarrier.Gen M' ↑S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M' ↑S) (v : CohCarrier.H1 M' H' 𝒪),
      op g • v = CohCarrier.opFamily M' H' ↑S 𝒪 g v)
    (hgen : Algebra.adjoin 𝒪 (Set.range op) = ⊤)
    (θbar : CohCarrier.Gen M' ↑S → k)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n) (πk : S'.CornerRing i₀ →ₐ[𝒪] k)
    (hπk : ∀ g : CohCarrier.Gen M' ↑S, πk (S'.toCornerRing i₀ (op g)) = θbar g)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) :
    ∃ τ : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)) →ₗ[S'.CornerRing i₀]
        ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)),
      (∀ m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)),
        ((τ m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀))) :
          CohCarrier.H1 M' H' 𝒪) = CohCarrier.charInvolution M' H' 𝒪 𝒪 (m : CohCarrier.H1 M' H' 𝒪)) ∧
      Nonempty
        (↥((LinearMap.ker (τ - LinearMap.id)).map
            (IsLocalRing.maximalIdeal (S'.CornerRing i₀) •
              (⊤ : Submodule (S'.CornerRing i₀)
                ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))).mkQ) ≃ₗ[S'.CornerRing i₀]
          ↥((LinearMap.ker (τ + LinearMap.id)).map
            (IsLocalRing.maximalIdeal (S'.CornerRing i₀) •
              (⊤ : Submodule (S'.CornerRing i₀)
                ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))).mkQ)) := by sorry
