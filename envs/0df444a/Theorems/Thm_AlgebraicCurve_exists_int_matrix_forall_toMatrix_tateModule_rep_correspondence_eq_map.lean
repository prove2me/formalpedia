-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map
-- name    : AlgebraicCurve.exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/a95acba4-2234-526d-a4de-d7185086be42
-- title:
--   One integral matrix for a correspondence on all Tate modules
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero and let $F$, $F'$ be fields equipped with $K$-algebra structures satisfying `IsCurveOver K F` and `IsCurveOver K F'`, that is: principal divisors behave as required by `HasPrincipalDivisors`, every place of $F$ (resp. $F'$) over $K$ has residue field finite over $K$, and the module of Kähler differentials $\Omega_{F/K}$ is free of rank $1$ over $F$ (resp. likewise for $F'$); assume in addition that $F$ is essentially of finite type over $K$. Let $\varphi, \psi : F \to F'$ be $K$-algebra homomorphisms whose underlying ring homomorphisms are integral, assume that $F'$ is a finite module over $F$ via $\psi$ (the predicate `FiniteAlong K ψ`), that the fundamental identity holds for the extension given by $\varphi$ (`FundamentalIdentityAlong K φ hφ`), and that the push-forward norm formula holds for the extension given by $\psi$ (`NormFormulaAlong K ψ hψfin`). Write $g = \mathrm{genusFF}\ K\ F = \dim_K H^1(0)$. Then there exists a $2g \times 2g$ matrix $M$ over $\mathbb{Z}$, with rows and columns indexed by `Fin (2 * genusFF K F)`, such that for every prime $p$ the $p$-adic Tate module of $\mathrm{Pic}^0(K,F)$ — the group of sequences $(x_n)_{n \in \mathbb{N}}$ in $\mathrm{Pic}^0$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ — admits a $\mathbb{Z}_p$-basis indexed by `Fin (2 * genusFF K F)` in which the $\mathbb{Z}_p$-linear endomorphism induced, via [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174), by the correspondence $\psi_* \circ \varphi^*$ on $\mathrm{Pic}^0(K,F)$ (regarded as an additive, hence $\mathbb{Z}$-linear, endomorphism) has matrix the entrywise image of $M$ under $\mathbb{Z} \to \mathbb{Z}_p$. In particular each such Tate module is free of rank $2g$ over $\mathbb{Z}_p$, and the single matrix $M$ is independent of $p$.
--
--   This is the integrality and $p$-independence statement for the action of a correspondence on the Tate modules of the degree-zero divisor class group of a function field: over the complex numbers the correspondence preserves the rank-$2g$ first homology lattice, and one integral matrix then describes its action for every prime. It is used to show that the rational Tate module of $\mathrm{Pic}^0$ has dimension $2g$ and that the characteristic polynomial of the correspondence on the Tate module is a monic integer polynomial independent of $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map.lean

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

theorem AlgebraicCurve.exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    {F' : Type} [Field F'] [Algebra K F'] [IsCurveOver K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψfin : FiniteAlong K ψ) (hFI : FundamentalIdentityAlong K φ hφ)
    (hNψ : NormFormulaAlong K ψ hψfin) :
    ∃ M : Matrix (Fin (2 * genusFF K F)) (Fin (2 * genusFF K F)) ℤ,
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ b : Module.Basis (Fin (2 * genusFF K F)) ℤ_[p] (TateModule p (Pic0 K F)),
          LinearMap.toMatrix b b (TateModule.rep p (Pic0 K F) (Module.End ℤ (Pic0 K F))
            (Pic0.correspondence φ ψ hφ hψ hFI hψfin hNψ).toIntLinearMap) =
            M.map (Int.castRingHom ℤ_[p]) := by sorry
