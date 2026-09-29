-- Prove2me | Theorems.Thm_CuspForm_IsNewform_inertia_labels_eq_or_eq_pow_of_isCuspidalOfType_subrepresentation_of_irreducible_odd_of_range
-- name    : CuspForm.IsNewform.inertia_labels_eq_or_eq_pow_of_isCuspidalOfType_subrepresentation_of_irreducible_odd_of_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/14f596df-7fdb-5a47-b302-10cb2d46cb17
-- title:
--   Inertia labels at q given by the cuspidal type θ or θ^q
-- statement:
--   Let $M\ge 1$, let $g$ be a weight-two cusp form on $\Gamma_0(M)$ which is a newform (a normalised Hecke eigenform whose eigensystem does not already occur at a proper divisor of $M$), and let $\lambda$ be a prime. Let $S$ be a finite set of naturals, let $O'$ be a complete discrete valuation domain of characteristic zero with finite residue field such that $\lambda$ lies in its maximal ideal, and assume $\lambda\neq 2$. Let $\chi_g$ be a ring homomorphism from the Hecke algebra [`CuspForm.heckeAlgebra M 2 S`](def/CuspForm_HeckeAlgebra.html#L18) to $\mathbb{C}$ with $\chi_g(T_\ell)=a_\ell(g)$ for every prime $\ell\nmid M$ with $\ell\notin S$, and let $\iota$ be a ring homomorphism from the range of $\chi_g$ into $O'$. Let $\rho$ be a rank-two adically continuous representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over $O'$ whose residual representation is irreducible and odd (every nontrivial involution has determinant $-1$), and assume that for each prime $\ell\nmid M$, $\ell\notin S$, each valuation subring $A\subset\overline{\mathbb{Q}}$ with $\ell\in A^{\mathrm{nonunits}}$ and each $\sigma$ inducing $x\mapsto x^{\ell}$ on the residue field of $A$, the characteristic polynomial of $\rho(\sigma)$ is $X^2-\iota(\chi_g(T_\ell))X+\ell$. Let $q$ be a prime with $q\neq\lambda$ and $\mathrm{ord}_q(M)=2$, let $\Phi$ be an adelic lift of $g$ on $\mathrm{GL}_2$ over the adeles of $\mathbb{Q}$, and let $P\subset\overline{\mathbb{Q}}$ be a valuation subring with $q\in P^{\mathrm{nonunits}}$. Let $j:O'\to O''$ be a ring homomorphism and $a,b$ functions from the Galois group to $O''^{\times}$ such that, for $\sigma$ in the inertia subgroup $I_P$ of $P$ over $\mathbb{Q}$, the image under $j$ of the characteristic polynomial of $\rho(\sigma)$ is $(X-a_\sigma)(X-b_\sigma)$, and $a,b$ are multiplicative on $I_P$. Let $V$ be a complex vector space with a $\mathrm{GL}_2(\mathbb{Q}_q)$-action commuting with the scalars, whose subspace of vectors fixed by the congruence subgroup [`FLT.SmoothVectors.gl2CongruenceSubgroup q 1`](def/RepTheory_GL2CongruenceSubgroup.html#L181) is finite dimensional, and let $f:V\to$ [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) $\Phi$ be an injective $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant linear map whose range is the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of the distinguished element of that span. Finally let $\theta:\mathbb{F}_{q^2}^{\times}\to\mathbb{C}^{\times}$ be a character and $W$ a subrepresentation of the representation [`LocalNewvector.gl2ReductionRep q V`](def/LocalNewvector_ReductionFunctor.html#L187) of $\mathrm{GL}_2(\mathbb{Z}/q)$ on those fixed vectors, such that $W$ is cuspidal of type $\theta$: its dimension is $q-1$, no nonzero vector is fixed by all upper unipotent matrices, the scalar matrices act trivially, and the characteristic polynomials on the nonsplit torus satisfy the stated identity against the induced representation. Then for every $\pi\in\overline{\mathbb{Q}}$ with $\pi^{q^2-1}=q$, every ring homomorphism $\iota_0:\mathbb{F}_{q^2}\to$ the residue field of $P$, and every ring homomorphism $e:O''\to\mathbb{C}$ with $e(j(\iota(x)))=x$ for all $x$ in the range of $\chi_g$, either $e(a_\sigma)=\theta(\alpha)$ for all $\sigma\in I_P$ and all $\alpha\in\mathbb{F}_{q^2}^{\times}$ with $\iota_0(\alpha)$ equal to the tame character $P.\mathrm{tameCharacter}\,\pi\,\sigma$, or $e(a_\sigma)=\theta(\alpha^{q})$ for all such $\sigma$ and $\alpha$.
--
--   This is the local-global compatibility step at a prime $q$ exactly dividing the level to the second power: the pair of inertial labels of the $\lambda$-adic representation attached to the newform is identified, after specialisation to $\mathbb{C}$, with the character $\theta$ of the cuspidal type occurring in the local component at $q$, up to the $q$-power conjugate. It refines the version in which the type is required of the whole space of $K(q)$-invariants, allowing instead an equivariant embedding of $V$ into the adelic span and a subrepresentation $W$, and it feeds the subsequent statement producing a nonzero map out of the local component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_inertia_labels_eq_or_eq_pow_of_isCuspidalOfType_subrepresentation_of_irreducible_odd_of_range.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem
CuspForm.IsNewform.inertia_labels_eq_or_eq_pow_of_isCuspidalOfType_subrepresentation_of_irreducible_odd_of_range
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (lam : ℕ) [Fact lam.Prime]
    (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O') (hlam2 : lam ≠ 2)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (iota : chig.range →+* O')
    (ρ : GaloisRepAdic O')
    (hirrbar : ρ.residual.IsIrreducible) (hodd : ρ.residual.IsOdd)
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) =
            X ^ 2 - C ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X
              + C ((ℓ : O')))
    (q : ℕ) [Fact q.Prime] (hqlam : q ≠ lam) (hqM : M.factorization q = 2)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦg : g.IsAdelicLiftOf Φ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {O'' : Type} [CommRing O''] (j : O' →+* O'')
    (a b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ)
    (hcp : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C ((a σ : O''ˣ) : O'')) * (X - C ((b σ : O''ˣ) : O'')))
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      a (σ * τ) = a σ * a τ ∧ b (σ * τ) = b σ * b τ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ
      ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) (hfinj : Function.Injective f)
    (hfrange : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (θ : (GaloisField q 2)ˣ →* ℂˣ)
    (W : Subrepresentation (LocalNewvector.gl2ReductionRep q V))
    (hθ : CuspidalType.IsCuspidalOfType θ W.toRepresentation) :
    (∀ (π : AlgebraicClosure ℚ), π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) →
        ∀ (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P) (e : O'' →+* ℂ),
          (∀ x : chig.range, e (j (iota x)) = (x : ℂ)) →
            (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
              ι (α : GaloisField q 2) = P.tameCharacter π σ → e ((a σ : O''ˣ) : O'') = ((θ α : ℂˣ) : ℂ)) ∨
            (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
              ι (α : GaloisField q 2) = P.tameCharacter π σ →
                e ((a σ : O''ˣ) : O'') = ((θ (α ^ q) : ℂˣ) : ℂ))) := by sorry
