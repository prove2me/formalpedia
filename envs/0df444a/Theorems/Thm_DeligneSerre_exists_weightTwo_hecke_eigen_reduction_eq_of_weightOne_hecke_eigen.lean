-- Prove2me | Theorems.Thm_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen
-- name    : DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/1a5f2a3d-2506-5f16-bc15-6c58dd51c630
-- title:
--   Weight-one mod-ℓ eigensystem realised in weight two
-- statement:
--   Let $N\ge 1$, let $\varepsilon$ be a Dirichlet character modulo $N$ with values in $\mathbb C$, and let $f$ be a cusp form of weight $1$ on $\Gamma_1(N)$ whose $q$-expansion coefficients $a_n =$ `qCoeff f n` (the coefficients of the $q$-expansion of width $1$) satisfy $a_1 = 1$ and, for every prime $p\nmid N$ and every $n\ge 0$, the Hecke relation $a_{pn} + \varepsilon(p)\,[p\mid n]\,a_{n/p} = a_p a_n$. Let $R\subseteq\mathbb C$ be a subring (a $\mathbb Z$-subalgebra) containing every $a_n$ and every value of $\varepsilon$, let $\kappa$ be a finite field and $\varphi\colon R\to\kappa$ a ring homomorphism. Then there exist an integer $M\ge 1$ whose prime divisors are exactly the primes dividing $N$ together with the characteristic of $\kappa$, a Dirichlet character $\eta$ modulo $M$, a nonzero cusp form $g$ of weight $2$ on $\Gamma_1(M)$ satisfying $g(\gamma\tau) = \eta(d)\,(c\tau+d)^2 g(\tau)$ for all $\gamma = \begin{pmatrix} a&b\\ c&d\end{pmatrix}\in\Gamma_0(M)$ and all $\tau$ in the upper half-plane, and a sequence $b\colon\mathbb N\to\mathbb C$ with $c_{pn}(g) + \eta(p)\,p\,[p\mid n]\,c_{n/p}(g) = b_p\,c_n(g)$ for every prime $p\nmid M$ and every $n$, where $c_n(g) =$ `qCoeff g n`; moreover there are a subring $R'\subseteq\mathbb C$ containing all values of $\eta$ and all $b_p$ for primes $p\nmid M$, and a ring homomorphism $\varphi'\colon R'\to\kappa$, such that $\varphi'(b_p) = \varphi(a_p)$ and $\varphi'(\eta(p))\cdot p = \varphi(\varepsilon(p))$ in $\kappa$ for every prime $p\nmid M$. No compatibility is required between $\varphi$ and $\varphi'$ beyond these two identities.
--
--   This is the weight-two variant of the weight-raising steps in Deligne and Serre's construction of the Galois representation attached to a weight-one eigenform: the mod-$\ell$ eigensystem of $f$ is matched, after twisting the nebentypus values by $p$, with the eigensystem of a genuine weight-two cusp form of level divisible only by the primes of $N$ and $\ell$. It is used to produce the residual Galois representation whose Frobenius characteristic polynomials are determined by the reduced weight-one eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen.lean

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ) :
    ∃ (M : ℕ) (_ : NeZero M),
      (∀ p : ℕ, p.Prime → (p ∣ M ↔ p ∣ N ∨ (p : κ) = 0)) ∧
      ∃ (η : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 2) (b : ℕ → ℂ),
        g ≠ 0 ∧ CuspForm.HasNebentypus η g ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
          ModularFormClass.qCoeff g (p * n) +
              η (p : ZMod M) * (p : ℂ) *
                (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
            b p * ModularFormClass.qCoeff g n) ∧
        ∃ (R' : Subalgebra ℤ ℂ) (φ' : R' →+* κ) (hη : ∀ x : ZMod M, η x ∈ R')
          (hb : ∀ p : ℕ, p.Prime → ¬ p ∣ M → b p ∈ R'),
          ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M),
            φ' ⟨b p, hb p hp hpM⟩ = φ ⟨ModularFormClass.qCoeff f p, hR p⟩ ∧
            φ' ⟨η (p : ZMod M), hη _⟩ * (p : κ) = φ ⟨ε (p : ZMod N), hε _⟩ := by sorry
