-- Prove2me | Theorems.Thm_CuspForm_IsNewform_finrank_monodromySpan_eigenPlane_tateModule_jZero_le_one_of_dvd
-- name    : CuspForm.IsNewform.finrank_monodromySpan_eigenPlane_tateModule_jZero_le_one_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/2113c71c-18a0-5733-8664-55b16f19a948
-- title:
--   Eigenplane monodromy span at λ ‖ M has dimension ≤ 1
-- statement:
--   Fix $M\ge 1$ and a cusp form $g$ of weight $2$ on $\Gamma_0(M)$ which is a newform, i.e. $g$ is a normalised eigenform (its $q$-coefficients satisfy $a_1=1$, multiplicativity at coprime indices and the usual recursions at prime powers) and for no proper divisor $M'\mid M$ does the eigensystem of $g$ away from $M$ occur in weight $2$ on $\Gamma_0(M')$. Let $\lambda$ be a prime, $S$ a finite set of naturals with $\lambda\in S$ containing every prime divisor of $M$, and suppose $\lambda\mid M$ but $\lambda^2\nmid M$. Let $O'$ be a complete discrete valuation domain of characteristic zero with finite residue field and $\lambda$ in its maximal ideal; let $\chi_g$ be a ring homomorphism to $\mathbb{C}$ from the Hecke algebra of level $M$, weight $2$, away from $S\setminus\{\lambda\}$ (the $\mathbb{Z}$-algebra generated inside $\operatorname{End}_{\mathbb{C}}$ of cusp forms by the operators $T_\ell$ for $\ell\nmid M$, $\ell\notin S\setminus\{\lambda\}$ and $U_q$ for $q\mid M$, $q\notin S\setminus\{\lambda\}$) sending each such $T_\ell$ to the $\ell$-th $q$-coefficient of $g$, and let $\iota$ be a ring homomorphism from the image of $\chi_g$ to $O'$. Let $O''$ be a further such discrete valuation ring which is a module-finite $O'$-algebra along a local homomorphism and a $\mathbb{Z}_\lambda$-algebra, and $K$ a fraction field of $O''$. Equip the degree-zero divisor class group $J_0(M)$ of the level-$M$ modular function field over $\overline{\mathbb{Q}}$ with its Hecke-algebra module structure, where the Hecke algebra is $\mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbb{Z}$, and let $T=\mathrm{TateModule}$ be the submodule of sequences $x:\mathbb{N}\to J_0(M)$ with $x_0=0$ and $\lambda\, x_{n+1}=x_n$. The assertion is then: given a $\mathbb{Z}_\lambda$-module structure on $T$ whose scalar multiplication is computed levelwise through the reductions $\mathbb{Z}_\lambda\to\mathbb{Z}/\lambda^n$, a monoid homomorphism $\rho_M$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\operatorname{End}_{O''}(O''\otimes_{\mathbb{Z}_\lambda}T)$ induced by the Galois action on $T$ on pure tensors, a ring homomorphism $T_M$ from the Hecke algebra to the same endomorphism ring induced by the Hecke action on pure tensors, and a $K$-submodule $W$ of $K\otimes_{O''}(O''\otimes_{\mathbb{Z}_\lambda}T)$ of dimension $2$ which is stable under every $\rho_M(\sigma)$ base-changed to $K$, on which the Hecke generator at each prime $\ell\nmid M$ with $\ell\notin S$ acts by the scalar $\iota(\chi_g(T_\ell))$ and the generator at $\lambda$ acts by $\iota(\chi_g(U_\lambda))$, and on which, for each such $\ell$ and each valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit in $A$ and each $\sigma$ which is a Frobenius at $\ell$ for $A$ (lying in the decomposition subgroup and acting on the residue field by $x\mapsto x^\ell$), the trace of $\rho_M(\sigma)|_W$ equals that same scalar $\iota(\chi_g(T_\ell))$: then for every valuation subring $A$ of $\overline{\mathbb{Q}}$ in which $\lambda$ is a non-unit, the $K$-span of the set of differences $(\rho_M(\sigma))_K w-w$, with $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$ and $w\in W$, has $K$-dimension at most $1$.
--
--   This is the rank-two local statement at a prime exactly dividing the level: the monodromy operators $\rho(\sigma)-1$ for $\sigma$ inertia at $\lambda$ span at most a line in the $g$-eigenplane, which is the Tate-module shadow of the toric line of the multiplicative reduction of $J_0(M)$ at a place above $\lambda$, the multiplicity-one bound using that $g$ is new at $\lambda$. It feeds the construction of the $\lambda$-adic representation attached to $g$ together with its ordinary (monodromy) line at $\lambda$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_finrank_monodromySpan_eigenPlane_tateModule_jZero_le_one_of_dvd.lean

import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve TensorProduct
set_option synthInstance.maxHeartbeats 400000

theorem CuspForm.IsNewform.finrank_monodromySpan_eigenPlane_tateModule_jZero_le_one_of_dvd
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (lam : ℕ) [Fact lam.Prime]
    (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (chig : CuspForm.heckeAlgebra M 2 ((↑S : Set ℕ) \ {lam}) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {lam})),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (iota : chig.range →+* O')
    (hlamS : lam ∈ S) (hMS : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S)
    (hlamM : lam ∣ M) (hlamM2 : ¬ lam ^ 2 ∣ M)
    (O'' : Type) [CommRing O''] [IsDomain O''] [IsDiscreteValuationRing O'']
    [IsAdicComplete (IsLocalRing.maximalIdeal O'') O''] [Finite (IsLocalRing.ResidueField O'')]
    [CharZero O''] [Algebra O' O''] [Module.Finite O' O''] [IsLocalHom (algebraMap O' O'')]
    [Algebra ℤ_[lam] O'']
    (K : Type) [Field K] [Algebra O'' K] [IsFractionRing O'' K] :
    letI := ModularCurve.heckeModuleBar M
    ∀ [Module ℤ_[lam] (ModularCurve.TateModule lam (JZero M))]
      (_hsmul : ∀ (a : ℤ_[lam]) (x : ModularCurve.TateModule lam (JZero M)) (n : ℕ),
        ((a • x : ModularCurve.TateModule lam (JZero M)) : ℕ → JZero M) n =
          (PadicInt.toZModPow n a).val • (x : ℕ → JZero M) n)
      (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
        Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M)))
      (_hρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x y : ModularCurve.TateModule lam (JZero M)),
        (y : ℕ → JZero M) = σ • (x : ℕ → JZero M) →
          ∀ a : O'', ρM σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] y)
      (TM : ModularCurve.HeckeAlg →+* Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M)))
      (_hT : ∀ (t : ModularCurve.HeckeAlg) (a : O'') (x : ModularCurve.TateModule lam (JZero M)),
        TM t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x))
      (W : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M))))
      (_hrank : Module.finrank K W = 2)
      (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W,
          (ρM σ).baseChange K w ∈ W)
      (_hHecke : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ))), ∀ w ∈ W,
          (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
            algebraMap O'' K (algebraMap O' O''
              ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓN
                (fun h => hℓS (Set.mem_of_mem_diff h))))) • w)
      (_htrace : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ))),
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ)) =
                algebraMap O'' K (algebraMap O' O''
                  ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓN
                (fun h => hℓS (Set.mem_of_mem_diff h))))))
      (_hUlam : ∀ w ∈ W,
          (TM (ModularCurve.heckeGen ⟨lam, Fact.out⟩)).baseChange K w =
            algebraMap O'' K (algebraMap O' O''
              ((iota.comp chig.rangeRestrict)
                (CuspForm.heckeAlgebra.U (Fact.out : lam.Prime) hlamM (by simp)))) • w),
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime lam →
      Module.finrank K (Submodule.span K
        {y : K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M)) |
          ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∃ w ∈ W, y = (ρM σ).baseChange K w - w}) ≤ 1 := by sorry
