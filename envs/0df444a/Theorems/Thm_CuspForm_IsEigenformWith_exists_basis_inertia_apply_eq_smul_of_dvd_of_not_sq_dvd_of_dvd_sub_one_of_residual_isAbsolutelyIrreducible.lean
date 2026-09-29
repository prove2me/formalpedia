-- Prove2me | Theorems.Thm_CuspForm_IsEigenformWith_exists_basis_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_sub_one_of_residual_isAbsolutelyIrreducible
-- name    : CuspForm.IsEigenformWith.exists_basis_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_sub_one_of_residual_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/d60a00c8-21c1-5cbd-99f6-6a015ab65886
-- title:
--   Inertia at a Taylor–Wiles prime exactly dividing the level
-- statement:
--   Fix $M\ge 1$, a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb{C}$, and a cusp form $h$ of weight $2$ on $\Gamma_1(M)$ which is an eigenform with nebentypus $\varepsilon$ in the sense of the project predicate: $a_1(h)=1$; for each prime $p\nmid M$ and each $n$, $a_{pn}(h)+\varepsilon(p)p^{k-1}\,[p\mid n]\,a_{n/p}(h)=a_p(h)a_n(h)$; for each prime $\ell\mid M$ and each $n$, $a_{\ell n}(h)=a_\ell(h)a_n(h)$; and $h(\gamma\tau)=\varepsilon(d)(c\tau+d)^{k}h(\tau)$ for $\gamma=\begin{pmatrix}*&*\\ c&d\end{pmatrix}\in\Gamma_0(M)$, where $a_n(h)$ denotes the $n$-th coefficient of the $q$-expansion. Let $\lambda$ be a prime, $S$ a finite set of naturals, and $O'$ a characteristic-zero discrete valuation domain, complete for its maximal-ideal adic topology, with finite residue field, such that $\lambda$ lies in the maximal ideal. Let $R$ be a commutative ring, $t\colon R\to\mathbb{C}$ an injective ring homomorphism, $\varphi\colon R\to O'$ a ring homomorphism, and $b,e\colon\mathbb{N}\to R$ with $t(b_\ell)=a_\ell(h)$ for all primes $\ell\nmid M$ with $\ell\notin S$, and $t(e_u)=\varepsilon(u)$ for all $u$ coprime to $M$. Let $\rho$ be an adic Galois representation over $O'$: a free finite $O'$-module $V$ of rank $2$ with a monoid homomorphism $\sigma\mapsto\rho(\sigma)$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (as $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$) to $\mathrm{End}_{O'}(V)$, such that for every $n$ some finite subextension $L/\mathbb{Q}$ has all its pointwise stabilisers acting trivially on $V$ modulo $\mathfrak{m}^n V$. Assume: for every prime $\ell\nmid M$ with $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ and acting as $x\mapsto x^{\ell}$ on the residue field of $A$, the characteristic polynomial of $\rho(\sigma)$ is $X^2-\varphi(b_\ell)X+\varphi(e_\ell)\ell$; the reduction $k'\otimes_{O'}V$ is absolutely irreducible, that is, its base change to $\overline{k'}$ has no Galois-stable submodule other than $\bot$ and $\top$. Let $q$ be a prime with $q\mid M$, $q^2\nmid M$, $\lambda\mid q-1$ and $t(b_q)=a_q(h)$; let $\mathrm{cyc}\colon\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to(\mathbb{Z}/q)^{\times}$ be a homomorphism with $\sigma\mu=\mu^{\mathrm{cyc}(\sigma)}$ for every $q$-th root of unity $\mu$; let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$, let $\phi_0$ lie in the decomposition subgroup of $P$ and act as $x\mapsto x^q$ on the residue field of $P$, and let $a_1\neq a_2$ in the residue field of $O'$ be such that the characteristic polynomial of $\rho(\phi_0)$ reduces to $(X-a_1)(X-a_2)$. Then $V$ has an $O'$-basis $(v_0,v_1)$ such that: for every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$, one has $\rho(\sigma)v_1=v_1$ and $\rho(\sigma)v_0=\varphi(e_u)v_0$ for every natural $u$ with $u\equiv\mathrm{cyc}(\sigma)\bmod q$ and $u\equiv 1\bmod M/q$; and for every $\tau$ lying in the decomposition subgroup of $P$ and acting as $x\mapsto x^q$ on the residue field of $P$, one has $\rho(\tau)v_1=\varphi(b_q)v_1$ and $\rho(\tau)v_0=c\,v_0$ for some $c\in O'$.
--
--   This is the weight-two local description at a prime dividing the level exactly once (Theorem 3.1(e) of Darmon–Diamond–Taylor, going back to Langlands and Carayol), recast for an arbitrary lattice with the prescribed Frobenius characteristic polynomials and absolutely irreducible reduction, in the shape used for Taylor–Wiles primes: the representation restricted to the decomposition group at $q$ splits into an unramified line on which Frobenius acts by the $U_q$-eigenvalue and a line on which inertia acts through the nebentypus composed with the mod-$q$ cyclotomic character. It feeds the analysis of the Galois representation carried by the Hecke ring at Taylor–Wiles level, through [`CuspForm.TWLevel.HeckeRing.exists_basis_inertia_apply_eq_diamond_smul_of_algHom`](thm.html#CuspForm.TWLevel.HeckeRing.exists_basis_inertia_apply_eq_diamond_smul_of_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsEigenformWith_exists_basis_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_sub_one_of_residual_isAbsolutelyIrreducible.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsEigenformWith.exists_basis_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_sub_one_of_residual_isAbsolutelyIrreducible
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
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M) (hq1 : lam ∣ q - 1)
    (hbq : toC (b q) = ModularFormClass.qCoeff h q)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ q = 1 → σ μ = μ ^ ((cyc σ : ZMod q).val))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (φ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ₀ : P.IsFrobeniusAt φ₀ q)
    (a₁ a₂ : IsLocalRing.ResidueField O') (ha : a₁ ≠ a₂)
    (hφ₀c : (LinearMap.charpoly (ρ.ρ φ₀)).map (IsLocalRing.residue O') = (X - C a₁) * (X - C a₂)) :
    ∃ bs : Module.Basis (Fin 2) O' ρ.V,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
        (∀ u : ℕ, (u : ZMod q) = ((cyc σ : (ZMod q)ˣ) : ZMod q) → (u : ZMod (M / q)) = 1 →
            ρ.ρ σ (bs 0) = φ (e u) • bs 0) ∧
        ρ.ρ σ (bs 1) = bs 1) ∧
      (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt τ q →
        ρ.ρ τ (bs 1) = φ (b q) • bs 1 ∧ ∃ c : O', ρ.ρ τ (bs 0) = c • bs 0) := by sorry
