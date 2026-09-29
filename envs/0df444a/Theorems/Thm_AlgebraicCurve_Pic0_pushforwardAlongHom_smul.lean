-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_pushforwardAlongHom_smul
-- name    : AlgebraicCurve.Pic0.pushforwardAlongHom_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/3819f556-b367-5639-87c3-b39c51425d5f
-- title:
--   Push-forward on Pic⁰ is equivariant for intertwined semilinear automorphisms
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ $K$-algebras, and let $g$ and $g'$ be elements of `SemilinearAut K F` and `SemilinearAut K F'` respectively, i.e. pairs consisting of a ring automorphism of the function field and a ring automorphism of $K$ compatible with the structure map (the automorphism of $F$, resp. $F'$, carries $\mathrm{alg}(a)$ to $\mathrm{alg}$ of the image of $a$ for every $a\in K$); such pairs act on places, hence on divisors $\mathrm{Divisor}\,K\,F=(\mathrm{Place}\,K\,F\to_{0}\mathbb{Z})$, on the degree-zero subgroup and on $\mathrm{Pic}^0 = \mathrm{degZero}/\mathrm{principal}$. Let $\varphi : F \to F'$ be a $K$-algebra map whose underlying ring map is integral, let `hfin` assert that $F'$ is a finite module over $F$ via $\varphi$, and let `hN` assert the push-forward norm formula along $\varphi$: for every nonzero $f\in F'$ and every divisor $D$ on $F'$ with $D(w)=\mathrm{ord}_w(f)$ at all places $w$, the push-forward of $D$ takes the value $\mathrm{ord}_v(N_{F'/F}f)$ at each place $v$ of $F$. Assume $g$ and $g'$ are intertwined along $\varphi$, i.e. $g'\cdot\varphi(x)=\varphi(g\cdot x)$ for all $x\in F$. Then for every class $x \in \mathrm{Pic}^0\,K\,F'$, the induced push-forward homomorphism `Pic0.pushforwardAlongHom` satisfies $\varphi_*(g'\cdot x)= g\cdot \varphi_*(x)$.
--
--   This is the statement that push-forward of degree-zero divisor classes along a finite integral extension of function fields is equivariant for semilinear automorphisms intertwined along the extension; applied with the arithmetic Galois automorphisms at two levels of a modular tower and $\varphi$ a degeneracy embedding, it yields Galois-equivariance of the degeneracy push-forwards between Jacobians. It is used in the Čerednik–Drinfeld constructions transporting Hecke correspondences and Frobenius data between levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_pushforwardAlongHom_smul.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

universe u

theorem AlgebraicCurve.Pic0.pushforwardAlongHom_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin)
    (hgg' : IntertwinesAlong φ.toRingHom g g') (x : Pic0 K F') :
    Pic0.pushforwardAlongHom φ hφ hfin hN (g' • x) = g • Pic0.pushforwardAlongHom φ hφ hfin hN x := by sorry
