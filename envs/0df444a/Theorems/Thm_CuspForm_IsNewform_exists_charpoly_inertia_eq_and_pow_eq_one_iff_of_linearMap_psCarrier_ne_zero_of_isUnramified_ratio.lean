-- Prove2me | Theorems.Thm_CuspForm_IsNewform_exists_charpoly_inertia_eq_and_pow_eq_one_iff_of_linearMap_psCarrier_ne_zero_of_isUnramified_ratio
-- name    : CuspForm.IsNewform.exists_charpoly_inertia_eq_and_pow_eq_one_iff_of_linearMap_psCarrier_ne_zero_of_isUnramified_ratio
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/68d01e8d-4ea9-5fc5-8634-e5d55f45de64
-- title:
--   Inertia at q≠λ: principal series with unramified ratio
-- statement:
--   Fix $M\ge 1$ and a weight-two cusp form $g$ on $\Gamma_0(M)$ which is a newform in the sense of the project (a normalised eigenform whose eigensystem does not already occur at a proper divisor of $M$); fix a prime $\lambda$, a finite set $S\subseteq\mathbb N$, and a characteristic-zero complete discrete valuation domain $O'$ with finite residue field in which $\lambda$ lies in the maximal ideal. Let $\chi_g$ be a ring homomorphism from the weight-two level-$M$ Hecke algebra away from $S$ to $\mathbb C$ with $\chi_g(T_\ell)$ equal to the $\ell$-th $q$-expansion coefficient of $g$ for every prime $\ell\nmid M$, $\ell\notin S$, let $\iota$ map the range of $\chi_g$ to $O'$, and let $\rho$ be an adically continuous representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on a free $O'$-module of rank $2$ such that, for every such $\ell$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$ and every $\sigma$ which is a Frobenius at $\ell$ for $A$ (that is, lies in the decomposition subgroup and acts as $x\mapsto x^{\ell}$ on the residue field), one has $\operatorname{charpoly}(\rho(\sigma)) = X^2-\iota(\chi_g(T_\ell))X+\ell$. Fix a prime $q\ne\lambda$, a nonzero adelic lift $\Phi$ of $g$ on $\mathrm{GL}_2$ of the adeles of $\mathbb Q$, characters $\mu_1,\mu_2:\mathbb Q_q^\times\to\mathbb C^\times$, and a nonzero $\mathrm{GL}_2(\mathbb Q_q)$-equivariant $\mathbb C$-linear map $f$ from the adelic span of $\Phi$ to the principal-series carrier attached to $(\mu_1,\mu_2)$; assume $\mu_1^{-1}\mu_2$ is unramified, i.e. trivial on all $u\in\mathbb Q_q^\times$ with $\|u\|=1$. Then there exist a local domain $O''$, an injective local ring homomorphism $j:O'\to O''$, and a function $a$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $O''^\times$ such that: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$ and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ over $\mathbb Q$, the image under $j$ of $\operatorname{charpoly}(\rho(\sigma))$ equals $(X-a(\sigma))(X-a(\sigma)^{-1})$; for every such $P$ and $\sigma$ there is a unit $u$ of $\mathbb Q_q$ with $\|u\|=1$ with $a(\sigma)^n=1\iff\mu_1(u)^n=1$ for all $n\in\mathbb N$; and conversely, for every such $u$ and every such $P$ there is a $\sigma$ in that inertia image satisfying the same equivalence of orders.
--
--   This is the principal-series case of local–global compatibility at a prime $q$ different from the residue characteristic $\lambda$, in the situation where the ratio $\mu_1^{-1}\mu_2$ of the two inducing characters is unramified, so that the eigenvalues of inertia at $q$ come in inverse pairs and are matched, order by order, with the values of $\mu_1$ on the units of $\mathbb Z_q$. It feeds the variant for level exactly divisible by $q^2$, [`CuspForm.IsNewform.exists_charpoly_inertia_eq_and_pow_eq_one_iff_of_linearMap_psCarrier_ne_zero_of_factorization_eq_two`](thm.html#CuspForm.IsNewform.exists_charpoly_inertia_eq_and_pow_eq_one_iff_of_linearMap_psCarrier_ne_zero_of_factorization_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_exists_charpoly_inertia_eq_and_pow_eq_one_iff_of_linearMap_psCarrier_ne_zero_of_isUnramified_ratio.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem CuspForm.IsNewform.exists_charpoly_inertia_eq_and_pow_eq_one_iff_of_linearMap_psCarrier_ne_zero_of_isUnramified_ratio
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (lam : ℕ) [Fact lam.Prime]
    (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (iota : chig.range →+* O')
    (ρ : GaloisRepAdic O')
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) =
            X ^ 2 - C ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X
              + C ((ℓ : O')))
    (q : ℕ) [Fact q.Prime] (hqlam : q ≠ lam)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hratio : LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂)) :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsLocalRing O'') (j : O' →+* O'')
      (_ : IsLocalHom j) (_ : Function.Injective j)
      (a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ),
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (LinearMap.charpoly (ρ.ρ σ)).map j =
            (X - C ((a σ : O''ˣ) : O'')) * (X - C (((a σ)⁻¹ : O''ˣ) : O''))) ∧
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ u ∈ LocalNewvector.higherUnits q 0,
          ∀ n : ℕ, a σ ^ n = 1 ↔ μ₁ u ^ n = 1) ∧
      (∀ u ∈ LocalNewvector.higherUnits q 0,
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
          ∃ σ ∈ P.inertiaSubgroupIn ℚ, ∀ n : ℕ, a σ ^ n = 1 ↔ μ₁ u ^ n = 1) := by sorry
