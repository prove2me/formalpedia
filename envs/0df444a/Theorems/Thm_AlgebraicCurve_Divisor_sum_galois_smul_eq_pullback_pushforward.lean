-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward
-- name    : AlgebraicCurve.Divisor.sum_galois_smul_eq_pullback_pushforward
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/f40d62f9-4e52-5caf-9067-7cfc02d836ff
-- title:
--   Galois trace of a divisor equals π^*π_*
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F'$ and $F$ both $K$-algebras and $F'$ an $F$-algebra forming a scalar tower over $K$, with $F'/F$ finite and Galois, and suppose $K \subseteq F'$ satisfies `HasPrincipalDivisors`: every nonzero $f \in F'$ admits a finitely supported $D : \mathrm{Place}\,K\,F' \to \mathbb{Z}$ with $D(v) = v.\mathrm{ord}(f)$ at every place $v$ and with $\deg D = 0$, where a place of $F'$ over $K$ is a valuation subring of $F'$ containing the image of $K$, not equal to $F'$ itself, and a principal ideal ring, and $\deg$ weights each place by its residue degree over $K$. Then for every divisor $D$ of $F'$ over $K$, i.e. every finitely supported $\mathbb{Z}$-valued function on these places, $$\sum_{\sigma \in \mathrm{Gal}(F'/F)} \bigl(\mathrm{ofAlgAut}(\sigma|_K)\bigr) \cdot D = \mathrm{pullback}_{F'}\bigl(\mathrm{pushforward}_F(D)\bigr),$$ the action of $\sigma$ being through the pair $(\sigma, \mathrm{id}_K)$ in the group of semilinear automorphisms acting on places by transport of valuation subrings, while $\mathrm{pushforward}_F$ sends a place $w$ to $\mathrm{inertiaDeg}(w)\,[\,w|_F\,]$, with $\mathrm{inertiaDeg}(w)$ the degree of the residue field of $w$ over that of $w|_F$, and $\mathrm{pullback}_{F'}$ sends a place $v$ of $F$ to $\sum_{w \mid v} e(w)\,[w]$, the sum over the fibre of $v$ in $F'$ weighted by ramification indices.
--
--   This is the standard identity expressing the conorm (pull-back of the norm, or trace) of a divisor in a finite Galois extension of function fields as the sum of its Galois conjugates; it rests on transitivity of the Galois action on a fibre together with the relation $g\,e\,f = [F':F]$. It is used in the study of the degree-zero divisor class group and its Tate module, and for the modular curves $X_H$ in computing sums of diamond operators acting on divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Divisor.sum_galois_smul_eq_pullback_pushforward
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [FiniteDimensional F F'] [IsGalois F F']
    [AlgebraicCurve.HasPrincipalDivisors K F'] (D : AlgebraicCurve.Divisor K F') :
    ∑ σ : F' ≃ₐ[F] F', AlgebraicCurve.SemilinearAut.ofAlgAut (σ.restrictScalars K) • D
      = AlgebraicCurve.Divisor.pullback F' (AlgebraicCurve.Divisor.pushforward F D) := by sorry
