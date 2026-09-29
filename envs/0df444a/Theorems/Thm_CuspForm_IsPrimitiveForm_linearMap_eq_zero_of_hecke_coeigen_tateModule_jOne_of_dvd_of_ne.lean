-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_linearMap_eq_zero_of_hecke_coeigen_tateModule_jOne_of_dvd_of_ne
-- name    : CuspForm.IsPrimitiveForm.linearMap_eq_zero_of_hecke_coeigen_tateModule_jOne_of_dvd_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/f5c544c1-a24c-57f1-a126-d8d40679b3a0
-- title:
--   No primitive form of level M occurs in Tₚ J₁(N) for N∣ M, N≠ M
-- statement:
--   Let $M\ge 1$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and let $g$ be a weight $2$ cusp form on $\Gamma_1(M)$ which is primitive with nebentypus $\varepsilon$, i.e. $g$ has $q$-coefficient $1$ at $n=1$, satisfies the Hecke recursion $a_{pn}(g)+\varepsilon(p)p^{k-1}\,[p\mid n]\,a_{n/p}(g)=a_p(g)a_n(g)$ for all primes $p\nmid M$, satisfies $a_{\ell n}(g)=a_\ell(g)a_n(g)$ for primes $\ell\mid M$, has nebentypus $\varepsilon$, and its eigenvalue packet $\bigl(a_n(g),\varepsilon(n)\bigr)$ occurs at no proper divisor level $M'\mid M$, $M'\neq M$ (no nonzero weight $2$ cusp form on $\Gamma_1(M')$ with some nebentypus satisfies the corresponding recursions with eigenvalues $a_p(g)$ for all primes outside a finite set). Let $N\ge 1$ divide $M$ with $N\neq M$, let $p$ be a prime, and assume the Hecke–diamond inputs [`ModularCurve.HeckeDiamondInputsAll N`](def/ModularCurve_X1HeckeModule.html#L58) (existence of the Hecke correspondences at each prime and of the diamond automorphisms for $d$ coprime to $N$, over $\overline{\mathbb{Q}}$) together with [`ModularCurve.HeckeDiamondCommuteBar N`](def/ModularCurve_X1HeckeModule.html#L54) (the corresponding operators on $\mathrm{Pic}^0$ of $X_1(N)$ over $\overline{\mathbb{Q}}$ commute pairwise). Let $S$ be a finite set of naturals, $K$ a field of characteristic zero that is a $\mathbb{Z}_p$-algebra, $R$ a commutative ring with an injective ring homomorphism $t\colon R\to\mathbb{C}$ and a ring homomorphism $\psi\colon R\to K$, and let $b,e\colon\mathbb{N}\to R$ satisfy $t(b_\ell)=a_\ell(g)$ and $t(e_\ell)=\varepsilon(\ell\bmod M)$ for every prime $\ell\nmid M$ with $\ell\notin S$. Give $J_1(N)=\mathrm{Pic}^0$ of the function field of $X_1(N)$ over $\overline{\mathbb{Q}}$ the module structure [`ModularCurve.heckeModuleOneBar N`](def/ModularCurve_X1HeckeModule.html#L129) over the polynomial Hecke algebra, and let $T_p J_1(N)$ be the group of compatible systems $(x_n)$ with $p^n x_n=0$ and $p\,x_{n+1}=x_n$, with the induced action of the Hecke algebra generators. Then for every $K$-vector space $W$, a $K$-linear map $f\colon K\otimes_{\mathbb{Z}_p}T_pJ_1(N)\to W$ such that for every prime $\ell\nmid M$ with $\ell\notin S$ and every $z$ one has $\psi(e_\ell)\,f(T_\ell z)=\psi(b_\ell)\,f(z)$ and $\psi(e_\ell)\,f(\langle\ell\rangle z)=f(z)$, where $T_\ell$ and $\langle\ell\rangle$ denote the base changes to $K$ of the operators induced by the generators `heckeGenOne` and `diamondGen` at $\ell$, is necessarily zero.
--
--   This is the Tate-module form of the primitivity (newness) of $g$ at level $M$: the eigenvalue packet of a primitive form of level $M$, read in $K$ through $\psi$, supports no nonzero co-eigen functional on $K\otimes_{\mathbb{Z}_p}T_pJ_1(N)$ for a proper divisor $N$ of $M$. It is used in the construction of the $p$-adic representation attached to $g$ and of its ordinary line and inertia behaviour at a prime dividing $M$ exactly once, where it serves to kill the contributions of the degeneracy maps from lower level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_linearMap_eq_zero_of_hecke_coeigen_tateModule_jOne_of_dvd_of_ne.lean

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem CuspForm.IsPrimitiveForm.linearMap_eq_zero_of_hecke_coeigen_tateModule_jOne_of_dvd_of_ne
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g)
    (N : ℕ) [NeZero N] (hNM : N ∣ M) (hne : N ≠ M) (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll N) (hcomm : ModularCurve.HeckeDiamondCommuteBar N)
    (S : Finset ℕ) (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* K)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)) :
    letI := ModularCurve.heckeModuleOneBar N
    ∀ (W : Type) [AddCommGroup W] [Module K W]
      (f : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne N) →ₗ[K] W),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        ∀ z : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne N),
          ψ (e ℓ) • f ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne N)
              (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)).baseChange K z) = ψ (b ℓ) • f z ∧
          ψ (e ℓ) • f ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne N)
              (ModularCurve.diamondGen ℓ)).baseChange K z) = f z) →
      f = 0 := by sorry
