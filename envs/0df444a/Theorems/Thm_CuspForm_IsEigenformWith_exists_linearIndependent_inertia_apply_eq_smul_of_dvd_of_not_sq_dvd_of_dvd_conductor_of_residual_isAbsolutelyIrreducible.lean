-- Prove2me | Theorems.Thm_CuspForm_IsEigenformWith_exists_linearIndependent_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_conductor_of_residual_isAbsolutelyIrreducible
-- name    : CuspForm.IsEigenformWith.exists_linearIndependent_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_conductor_of_residual_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/8f61ead1-85ff-50e2-9c93-25710b76e9d2
-- title:
--   Inertia eigenlines at q ‖ M dividing the nebentypus conductor
-- statement:
--   Fix $M\ge 1$, a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb{C}$, and a cusp form $h$ of weight $2$ on $\Gamma_1(M)$ which is an eigenform with nebentypus $\varepsilon$ in the coefficient sense: the $q$-expansion coefficients satisfy $a_1(h)=1$, $a_{pn}(h)+\varepsilon(p)p^{k-1}\,[p\mid n]\,a_{n/p}(h)=a_p(h)a_n(h)$ for primes $p\nmid M$ and all $n$, $a_{\ell n}(h)=a_\ell(h)a_n(h)$ for primes $\ell\mid M$ and all $n$, and $h(\gamma\tau)=\varepsilon(\gamma_{11})(\gamma_{10}\tau+\gamma_{11})^k h(\tau)$ for $\gamma\in\Gamma_0(M)$ (here $k=2$). Let $\lambda$ be a prime, $S$ a finite set of naturals, and $O'$ a complete discrete valuation ring of characteristic zero with finite residue field in whose maximal ideal $\lambda$ lies. The Hecke data are read in $O'$ through a commutative ring $R$, an injective $\mathrm{toC}\colon R\to\mathbb{C}$, a homomorphism $\varphi\colon R\to O'$ and elements $b_n,e_n\in R$ with $\mathrm{toC}(b_\ell)=a_\ell(h)$ for primes $\ell\nmid M$, $\ell\notin S$, and $\mathrm{toC}(e_u)=\varepsilon(u)$ for all $u$ coprime to $M$. Let $\rho$ be a [`GaloisRepAdic O'`](def/GaloisRep_Adic.html#L16): a free finite $O'$-module $V$ of rank two with a homomorphism $\rho$ from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\mathrm{End}_{O'}(V)$ which is adically continuous (for each $n$ there is a finite $L/\mathbb{Q}$ in $\overline{\mathbb{Q}}$ with $\rho(\sigma)v-v\in\mathfrak{m}^n V$ whenever $\sigma$ fixes $L$ pointwise). Assume that for every prime $\ell\nmid M$ with $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ in its nonunits, and every $\sigma$ lying in the decomposition group of $A$ and inducing $x\mapsto x^{\ell}$ on the residue field, $\mathrm{charpoly}(\rho(\sigma))=X^2-\varphi(b_\ell)X+\varphi(e_\ell)\ell$; and that the residual representation $\mathrm{ResidueField}(O')\otimes_{O'}V$ is absolutely irreducible, i.e. after base change to the algebraic closure of the residue field its only Galois-stable submodules are $0$ and the whole space. Let $q$ be a prime with $q\ne\lambda$, $q\mid M$, $q^2\nmid M$, $q\mid\mathrm{cond}(\varepsilon)$ and $\mathrm{toC}(b_q)=a_q(h)$, and let $\mathrm{cyc}\colon \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})\to(\mathbb{Z}/q)^\times$ be a homomorphism with $\sigma\mu=\mu^{\mathrm{cyc}(\sigma)}$ for all $q$-th roots of unity $\mu$. Then for every valuation subring $P$ of $\overline{\mathbb{Q}}$ having $q$ among its nonunits there are $v_0,v_1\in V$ with $\![v_0,v_1]$ linearly independent over $O'$ such that every $\sigma$ in the inertia subgroup at $P$ (the image in the Galois group of the inertia subgroup of the decomposition group of $P$) satisfies $\rho(\sigma)v_0=\varphi(e_u)v_0$ for every natural number $u$ with $u\equiv\mathrm{cyc}(\sigma)\pmod q$ and $u\equiv 1\pmod{M/q}$, and $\rho(\sigma)v_1=v_1$; and every $\tau$ lying in the decomposition group of $P$ and inducing $x\mapsto x^{q}$ on the residue field satisfies $\rho(\tau)v_1=\varphi(b_q)v_1$ and $\rho(\tau)v_0=c\,v_0$ for some $c\in O'$. The pair $v_0,v_1$ is asserted to be linearly independent, not to be a basis of $V$.
--
--   This is the local description at a prime $q$ exactly dividing the level and dividing the conductor of the nebentypus — the principal series case of Carayol's and Langlands' local-global compatibility, appearing as one case of Theorem 3.1 of the Darmon–Diamond–Taylor survey — transposed from newforms to an arbitrary weight-two $\Gamma_1(M)$ eigenform and to an arbitrary rank-two lattice with residually absolutely irreducible reduction, identified only by its Frobenius characteristic polynomials outside $M$ and $S$. It feeds the version in which the two vectors form a basis, the shape in which the condition at $q$ enters the deformation-theoretic arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsEigenformWith_exists_linearIndependent_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_conductor_of_residual_isAbsolutelyIrreducible.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsEigenformWith.exists_linearIndependent_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_conductor_of_residual_isAbsolutelyIrreducible
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (lam : ℕ) [Fact lam.Prime] (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ u : ℕ, u.Coprime M → toC (e u) = ε (u : ZMod M))
    (ρ : GaloisRepAdic O')
    (hρ : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (φ (b ℓ)) * X + C (φ (e ℓ) * (ℓ : O')))
    (hirr : ρ.residual.IsAbsolutelyIrreducible)
    (q : ℕ) (hq : q.Prime) (hqlam : q ≠ lam) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M)
    (hqε : q ∣ ε.conductor)
    (hbq : toC (b q) = ModularFormClass.qCoeff h q)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ q = 1 → σ μ = μ ^ ((cyc σ : ZMod q).val)) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∃ v₀ v₁ : ρ.V, LinearIndependent O' ![v₀, v₁] ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (∀ u : ℕ, (u : ZMod q) = ((cyc σ : (ZMod q)ˣ) : ZMod q) → (u : ZMod (M / q)) = 1 →
              ρ.ρ σ v₀ = φ (e u) • v₀) ∧
          ρ.ρ σ v₁ = v₁) ∧
        (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt τ q →
          ρ.ρ τ v₁ = φ (b q) • v₁ ∧ ∃ c : O', ρ.ρ τ v₀ = c • v₀) := by sorry
