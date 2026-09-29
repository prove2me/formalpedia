-- Prove2me | Theorems.Thm_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen
-- name    : DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/fda07c68-6f16-5bd0-b981-aa8db624396e
-- title:
--   Deligne–Serre: residual representation of a weight-one eigenform
-- statement:
--   Let $N$ be a nonzero natural number, $\varepsilon$ a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and $f$ a cusp form of weight $1$ on $\Gamma_1(N)$, whose $q$-expansion coefficients are written $a_n =$ [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19). Assume $a_1 = 1$ and that for every prime $p \nmid N$ and every $n$, $a_{pn} + \varepsilon(p)\,[p \mid n]\,a_{n/p} = a_p a_n$. Let $R \subseteq \mathbb{C}$ be a $\mathbb{Z}$-subalgebra containing $a_p$ for every prime $p \nmid N$ and all values of $\varepsilon$, let $k$ be a finite field and $\varphi \colon R \to k$ a ring homomorphism. Then there is a group homomorphism $\rho$ from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\mathrm{GL}_2(k)$ such that: $\rho$ is trivial on all automorphisms fixing some finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ pointwise; the associated representation of the Galois group on $k^2$ is semisimple; and for every prime $p \nmid N$ with $p \neq 0$ in $k$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, the homomorphism $\rho$ kills the image in the Galois group of the inertia subgroup of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^p$ satisfies $\mathrm{charpoly}(\rho(\sigma)) = X^2 - \varphi(a_p) X + \varphi(\varepsilon(p))$.
--
--   This is Théorème 6.7 of Deligne–Serre in weight one, in its residual form: the semisimple mod-$\ell$ two-dimensional representation attached to a weight-one Hecke eigenform, realised over the prescribed finite field $k$ via $\varphi$, unramified outside $N$ and the characteristic of $k$. It is obtained from the weight-two case by multiplication by an Eisenstein series and an eigenvalue-lifting argument, and feeds into the construction of the complex (characteristic-zero) representation attached to such an eigenform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup Polynomial
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (k : Type) [Field k] [Finite k] (φ : R →+* k) :
    ∃ ρ : Γℚ →* GL (Fin 2) k, GaloisFactorsThroughFiniteLevel ρ ∧
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), (p : k) ≠ 0 →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).charpoly =
              X ^ 2 - C (φ ⟨ModularFormClass.qCoeff f p, hR p hp hpN⟩) * X +
                C (φ ⟨ε (p : ZMod N), hε _⟩) := by sorry
