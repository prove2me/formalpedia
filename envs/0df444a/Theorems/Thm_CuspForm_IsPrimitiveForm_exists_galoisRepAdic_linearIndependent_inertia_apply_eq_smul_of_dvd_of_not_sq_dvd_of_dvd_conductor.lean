-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_linearIndependent_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_conductor
-- name    : CuspForm.IsPrimitiveForm.exists_galoisRepAdic_linearIndependent_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_conductor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/29bddcf8-a2b4-57d2-bd34-27eec2b040d4
-- title:
--   Inertia-fixed and nebentypus lines at q exactly dividing M
-- statement:
--   Let $M\ge 1$, let $\varepsilon$ be a Dirichlet character mod $M$ with values in $\mathbb{C}$, and let $h$ be a cusp form of weight $2$ on $\Gamma_1(M)$ which is primitive for $\varepsilon$: its $q$-expansion coefficients satisfy $a_1(h)=1$, the Hecke relations $a_{p n}(h)+\varepsilon(p)p^{k-1}[p\mid n]a_{n/p}(h)=a_p(h)a_n(h)$ for primes $p\nmid M$, the multiplicativity $a_{\ell n}(h)=a_\ell(h)a_n(h)$ for primes $\ell\mid M$, and $h$ has nebentypus $\varepsilon$; moreover, for no proper divisor $M'$ of $M$ does the eigenpacket $(a_n(h),\varepsilon(n))$ occur at level $M'$ in weight $2$. Let $\lambda$ be a prime lying in a finite set $S\subseteq\mathbb{N}$, and let $O'$ be a characteristic-zero complete discrete valuation ring with finite residue field whose maximal ideal contains $\lambda$. The Hecke data are read in $O'$ through a commutative ring $R$, an injective ring homomorphism $\mathrm{toC}\colon R\to\mathbb{C}$, a ring homomorphism $\varphi\colon R\to O'$, and families $b,e\colon\mathbb{N}\to R$ with $\mathrm{toC}(b_\ell)=a_\ell(h)$ and $\mathrm{toC}(e_\ell)=\varepsilon(\ell)$ for all primes $\ell\nmid M$ with $\ell\notin S$. Let $q$ be a prime with $q\neq\lambda$, $q\mid M$, $q^2\nmid M$, $q\mid\operatorname{cond}\varepsilon$ and $\mathrm{toC}(b_q)=a_q(h)$, and let $\mathrm{cyc}\colon\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to(\mathbb{Z}/q)^\times$ be a group homomorphism with $\sigma\mu=\mu^{\mathrm{cyc}(\sigma)}$ for all $\mu\in\overline{\mathbb{Q}}$ with $\mu^q=1$. Then there is a characteristic-zero complete discrete valuation ring $O''$ with finite residue field, module-finite over $O'$ with injective local structure map $O'\to O''$, and a two-dimensional free $O''$-representation $\rho$ of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ which is $\mathfrak{m}$-adically continuous (for each $n$ some finite subextension $L/\mathbb{Q}$ of $\overline{\mathbb{Q}}$ has $\rho(\sigma)v-v\in\mathfrak{m}^n V$ for all $\sigma$ fixing $L$ pointwise), such that: (i) for every prime $\ell\nmid M$ with $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma$ in the decomposition group of $A$ acting as $x\mapsto x^\ell$ on the residue field of $A$, the characteristic polynomial of $\rho(\sigma)$ is $X^2-\varphi(b_\ell)X+\varphi(e_\ell)\ell$ (images in $O''$); and (ii) for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$ there are $v_0,v_1\in V$, linearly independent over $O''$, such that every $\sigma$ in the image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ fixes $v_1$ and satisfies $\rho(\sigma)v_0=\varphi(e_u)\,v_0$ for every prime $u\nmid M$, $u\notin S$, with $u\equiv\mathrm{cyc}(\sigma)\pmod q$ and $u\equiv 1\pmod{M/q}$, while every $\tau$ in the decomposition group of $P$ acting as $x\mapsto x^q$ on the residue field of $P$ satisfies $\rho(\tau)v_1=\varphi(b_q)\,v_1$ and $\rho(\tau)v_0=c\,v_0$ for some $c\in O''$.
--
--   This is the case "$q$ exactly divides the level and divides the conductor of the nebentypus" of the local–global description of the $\lambda$-adic representation attached to a weight-two newform, in the shape of Carayol's theorem and of Theorem 3.1 of Darmon–Diamond–Taylor: the restriction to a decomposition group at $q$ has an unramified line on which Frobenius acts by $a_q(h)$ and a complementary line on which inertia acts through the nebentypus character at $q$. It is used in the deduction of the corresponding statement for the residual representation when the latter is absolutely irreducible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_linearIndependent_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_conductor.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsPrimitiveForm.exists_galoisRepAdic_linearIndependent_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_conductor
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsPrimitiveForm ε h)
    (lam : ℕ) [Fact lam.Prime] (S : Finset ℕ) (hlamS : lam ∈ S)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (q : ℕ) (hq : q.Prime) (hqlam : q ≠ lam) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M)
    (hqε : q ∣ ε.conductor)
    (hbq : toC (b q) = ModularFormClass.qCoeff h q)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ q = 1 → σ μ = μ ^ ((cyc σ : ZMod q).val)) :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsDiscreteValuationRing O'')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O'') O'')
        (_ : Finite (IsLocalRing.ResidueField O'')) (_ : CharZero O'')
        (_ : Algebra O' O'') (_ : Module.Finite O' O'') (_ : IsLocalHom (algebraMap O' O'')),
      Function.Injective (algebraMap O' O'') ∧
      ∃ ρ : GaloisRepAdic O'',
        (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) =
                X ^ 2 - C (algebraMap O' O'' (φ (b ℓ))) * X
                  + C (algebraMap O' O'' (φ (e ℓ) * (ℓ : O')))) ∧
        (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
          ∃ v₀ v₁ : ρ.V, LinearIndependent O'' ![v₀, v₁] ∧
            (∀ σ ∈ P.inertiaSubgroupIn ℚ,
              (∀ u : ℕ, u.Prime → ¬ u ∣ M → u ∉ S →
                  (u : ZMod q) = ((cyc σ : (ZMod q)ˣ) : ZMod q) → (u : ZMod (M / q)) = 1 →
                    ρ.ρ σ v₀ = algebraMap O' O'' (φ (e u)) • v₀) ∧
              ρ.ρ σ v₁ = v₁) ∧
            (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt τ q →
              ρ.ρ τ v₁ = algebraMap O' O'' (φ (b q)) • v₁ ∧ ∃ c : O'', ρ.ρ τ v₀ = c • v₀)) := by sorry
