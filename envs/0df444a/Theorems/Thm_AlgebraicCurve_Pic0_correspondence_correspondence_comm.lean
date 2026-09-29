-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_correspondence_correspondence_comm
-- name    : AlgebraicCurve.Pic0.correspondence_correspondence_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/cd5f9a1a-6c65-5a24-905e-1eac4ab3c441
-- title:
--   Divisor-level commuting correspondences commute on Pic⁰
-- statement:
--   Let $K$, $F$, $F_1$, $F_2$ be fields with $F$, $F_1$, $F_2$ algebras over $K$, and assume that $F_1$ and $F_2$ have principal divisors in the sense that for every nonzero $f$ in the field there is a finitely supported function on the places of that field over $K$ whose value at each place $v$ is $v$-adic order of $f$ and whose degree is $0$. Let $\varphi,\psi : F \to F_1$ and $\varphi',\psi' : F \to F_2$ be $K$-algebra maps whose underlying ring homomorphisms are integral, so that each makes the target an integral algebra over $F$. Assume the fundamental identity along $\varphi$ and along $\varphi'$ (used to see that the divisor-level correspondences preserve degree zero), and that $F_1$ is a finite module over $F$ via $\psi$ and $F_2$ is a finite module over $F$ via $\psi'$, together with the pushforward norm formula for these two finite extensions (used to see that principal divisors go to principal divisors). Write $T = \psi_* \varphi^*$ and $T' = \psi'_* \varphi'^*$ for the resulting endomorphisms of the group $\mathrm{Divisor}\,K\,F$ of finitely supported $\mathbb{Z}$-valued functions on the places of $F$ over $K$, and for their descents to $\mathrm{Pic}^0(F/K)$, the quotient of degree-zero divisors by principal degree-zero divisors. If $T \circ T' = T' \circ T$ holds on every divisor of $F$, then for each $x \in \mathrm{Pic}^0(F/K)$ the descended operators satisfy $T(T'(x)) = T'(T(x))$.
--
--   This is the transfer of commutation of two divisorial correspondences on a curve from the level of divisors to the level of the degree-zero divisor class group; the hypothesis assumed is commutation on all divisors, which is stronger than commutation on degree-zero classes. It is used to obtain commutation of Hecke operators on $\mathrm{Pic}^0$ of modular curves, in [`ModularCurve.heckeOperatorBar_comm_of_heckeExchangeAt`](thm.html#ModularCurve.heckeOperatorBar_comm_of_heckeExchangeAt), [`ModularCurve.heckeOperatorHAlong_comm`](thm.html#ModularCurve.heckeOperatorHAlong_comm) and [`ModularCurve.heckeOperatorOneBar_comm`](thm.html#ModularCurve.heckeOperatorOneBar_comm), once the corresponding identity has been established for divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_correspondence_correspondence_comm.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.correspondence_correspondence_comm {K F F₁ F₂ : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] (φ ψ : F →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) (hFI' : FundamentalIdentityAlong K φ' hφ') (hfin' : FiniteAlong K ψ') (hN' : NormFormulaAlong K ψ' hfin') (hcomm : ∀ D : Divisor K F, Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) = Divisor.correspondence φ' ψ' hφ' hψ' (Divisor.correspondence φ ψ hφ hψ D)) (x : Pic0 K F) : Pic0.correspondence φ ψ hφ hψ hFI hfin hN (Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' x) = Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) := by sorry
