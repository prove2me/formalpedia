-- Prove2me | Theorems.Thm_DeligneSerre_exists_galoisRep_of_weightOne_qCoeff_hecke_eigen
-- name    : DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/242f83e6-209a-5038-a6c0-380b94fddb43
-- title:
--   Deligne–Serre: Galois representation of a weight-one eigenform
-- statement:
--   Let $N$ be a nonzero natural number, $\varepsilon$ a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and $f$ a cusp form of weight $1$ for $\Gamma_1(N)$; write $a_n =$ [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19) for the $n$-th coefficient of the $q$-expansion of $f$ (of width $1$). Assume $a_1 = 1$ and that for every prime $p \nmid N$ and every $n \ge 0$ one has $a_{pn} + \varepsilon(p)\,[p \mid n]\,a_{n/p} = a_p a_n$, where the second term is read as $0$ when $p \nmid n$. The conclusion asserts the existence of a group homomorphism $\rho \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{C})$ (the Galois group being the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`) such that: (i) $\rho$ is trivial on the automorphisms fixing some intermediate field $L$ with $L/\mathbb{Q}$ finite, pointwise; (ii) the associated representation of the Galois group on $\mathbb{C}^2$ is irreducible; and (iii) for every prime $p \nmid N$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, the image in the Galois group of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in $\ker\rho$, and for every $\sigma$ in the decomposition subgroup of $A$ acting on the residue field of $A$ by $x \mapsto x^p$ one has $\operatorname{tr}\rho(\sigma) = a_p$ and $\det\rho(\sigma) = \varepsilon(p \bmod N)$. No oddness assumption on $\varepsilon$ is imposed.
--
--   This is Théorème 4.1 of Deligne–Serre, attaching to a normalised weight-one Hecke eigenform of level $N$ and nebentypus $\varepsilon$ an irreducible complex two-dimensional Galois representation with finite image, unramified outside $N$ and with prescribed Frobenius traces and determinants. It is used in the Langlands–Tunnell input to modularity, where it supplies the complex representation attached to a weight-one cusp form constructed there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_galoisRep_of_weightOne_qCoeff_hecke_eigen.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ ρ : Γℚ →* GL (Fin 2) ℂ, GaloisFactorsThroughFiniteLevel ρ ∧
      (Deformation.matrixRepresentation ρ).IsIrreducible ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = ModularFormClass.qCoeff f p ∧
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = ε (p : ZMod N) := by sorry
