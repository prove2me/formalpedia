-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul
-- name    : AlgebraicCurve.SemilinearAut.pic0_correspondence_swap_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/7dbedf1f-cffd-55ca-9ca1-13fe9e40555f
-- title:
--   Swapping the legs of a correspondence on Pic⁰
-- statement:
--   Let $K$ be a field and $F$, $F'$ two field extensions of $K$, with $F'$ satisfying `HasPrincipalDivisors K F'`, i.e. every nonzero $f \in F'$ has a divisor of degree $0$ whose coefficient at each place is $\mathrm{ord}_v(f)$; here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ and a principal ideal ring, a divisor is a finitely supported $\mathbb{Z}$-valued function on places, and $\mathrm{Pic}^0(F/K)$ is the group of degree-zero divisors modulo the principal ones. Let $g = (g_F, g_K)$ and $g' = (g_{F'}, g_K')$ be semilinear automorphisms, that is, pairs consisting of a ring automorphism of $F$ (resp. $F'$) and one of $K$ compatible with the structure map, acting on places, hence on divisors and on $\mathrm{Pic}^0$. Let $\varphi, \psi \colon F \to F'$ be $K$-algebra maps, each integral as a ring homomorphism, and assume the fundamental identity along $\varphi$ and along $\psi$, and module-finiteness of $F'$ over $F$ together with the pushforward norm formula along $\varphi$ and along $\psi$, so that $\psi_* \circ \varphi^*$ and $\varphi_* \circ \psi^*$ induce endomorphisms of $\mathrm{Pic}^0(F/K)$. Assume $g'$ exchanges the two legs over $g$: $g' \cdot \varphi(x) = \psi(g \cdot x)$ and $g' \cdot \psi(x) = \varphi(g \cdot x)$ for all $x \in F$. Then for every $c \in \mathrm{Pic}^0(F/K)$ one has $(\psi_* \circ \varphi^*)(g \cdot c) = g \cdot (\varphi_* \circ \psi^*)(c)$.
--
--   This is the abstract form of the Atkin–Lehner relation between a Hecke correspondence and its transpose under an involution interchanging the two degeneracy maps. It is applied with $F$ and $F'$ the function fields of modular curves of level $\Gamma_H(M)$ and $\Gamma_H(M) \cap \Gamma_0(M\ell)$, the two legs given by the inclusion and by $q \mapsto q^{\ell}$, and $(g, g')$ the Fricke involutions, in the construction of the Fricke automorphism of the function field over $\overline{\mathbb{Q}}$ and its compatibility with the Galois and correspondence actions on $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.SemilinearAut.pic0_correspondence_swap_smul {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F}
    {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)
    (h₁ : ∀ x : F, g' • (φ x) = ψ (g • x)) (h₂ : ∀ x : F, g' • (ψ x) = φ (g • x))
    (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ (g • c)
      = g • Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ c := by sorry
