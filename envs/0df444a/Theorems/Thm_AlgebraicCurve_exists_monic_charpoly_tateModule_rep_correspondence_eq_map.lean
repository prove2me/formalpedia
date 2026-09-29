-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_monic_charpoly_tateModule_rep_correspondence_eq_map
-- name    : AlgebraicCurve.exists_monic_charpoly_tateModule_rep_correspondence_eq_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/5121a3f7-02d8-59de-b695-be96dfad34bb
-- title:
--   A single integral characteristic polynomial for a correspondence on Tₚ(Pic⁰)
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero and let $F$, $F'$ be fields that are $K$-algebras, essentially of finite type over $K$, each satisfying `IsCurveOver K F`, i.e. $K$-divisors admit the principal-divisor property, every place of $F/K$ has residue field of finite $K$-dimension, and $\Omega_{F/K}$ is free of rank one over $F$. Let $\varphi,\psi : F \to F'$ be $K$-algebra maps whose underlying ring homomorphisms are integral, assume $F'$ is a finite module over $F$ along $\psi$, the fundamental identity holds along $\varphi$, and the pushforward norm formula holds along $\psi$. Write $g = \mathrm{genusFF}\,K\,F$, the $K$-dimension of $H^1$ of the zero divisor, and let $h$ be the endomorphism `Pic0.correspondence` of $\mathrm{Pic}^0(F/K)$ obtained by pulling divisor classes back along $\varphi$ and pushing forward along $\psi$. The assertion: there is a monic $\chi \in \mathbb{Z}[X]$ with $\deg\chi = 2g$ such that for every prime $p$ and every $\mathbb{Z}_p$-basis $b$ of the Tate module $T_p(\mathrm{Pic}^0(F/K))$ indexed by $\mathrm{Fin}(2g)$, the characteristic polynomial of the matrix in $b$ of the $\mathbb{Z}_p$-linear operator induced by $h$ on $T_p$ equals the image of $\chi$ in $\mathbb{Z}_p[X]$. Here $T_p(M)$ is the group of sequences $(x_n)$ in $M$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$. For primes at which no such basis exists the inner clause is vacuous.
--
--   Classically this is Weil's characteristic polynomial of the endomorphism of the Jacobian attached to a correspondence: a monic integer polynomial of degree $2g$ independent of the prime, which governs the action on every $p$-adic Tate module. It is used in the study of the Hecke action on modular curves, being cited by [`ModularCurve.exists_pow_smul_eq_zero_of_forall_tateModule_eq_zero`](thm.html#ModularCurve.exists_pow_smul_eq_zero_of_forall_tateModule_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_monic_charpoly_tateModule_rep_correspondence_eq_map.lean

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve

theorem AlgebraicCurve.exists_monic_charpoly_tateModule_rep_correspondence_eq_map
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    {F' : Type} [Field F'] [Algebra K F'] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψfin : FiniteAlong K ψ) (hFI : FundamentalIdentityAlong K φ hφ)
    (hNψ : NormFormulaAlong K ψ hψfin) :
    ∃ χ : Polynomial ℤ, χ.Monic ∧ χ.natDegree = 2 * genusFF K F ∧
      ∀ (p : ℕ) [Fact p.Prime]
        (b : Module.Basis (Fin (2 * genusFF K F)) ℤ_[p] (TateModule p (Pic0 K F))),
        (LinearMap.toMatrix b b (TateModule.rep p (Pic0 K F) (Module.End ℤ (Pic0 K F))
          (Pic0.correspondence φ ψ hφ hψ hFI hψfin hNψ).toIntLinearMap)).charpoly =
          χ.map (Int.castRingHom ℤ_[p]) := by sorry
