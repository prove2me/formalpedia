-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
-- name    : AlgebraicCurve.Divisor.mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/3482de20-c1d3-5a1d-94a5-f69d785aa4ca
-- title:
--   Reduction compatible with conorm on degree-zero divisors
-- statement:
--   Let $K$, $F_1$, $F_2$ be fields with $F_1$, $F_2$ extensions of $K$, and $k$, $C_1$, $C_2$ fields with $C_1$, $C_2$ extensions of $k$, where $F_2/K$ and $C_2/k$ satisfy `HasPrincipalDivisors`, i.e. every nonzero element $f$ has a degree-zero divisor whose coefficient at each place is the order of $f$ there. Let $\varphi\colon F_1\to F_2$ be a $K$-algebra map whose underlying ring map is integral, and $\bar\varphi\colon C_1\to C_2$ a $k$-algebra map whose underlying ring map is integral; write $\varphi^{*},\varphi_{*}$ and $\bar\varphi^{*},\bar\varphi_{*}$ for the induced pull-back and push-forward homomorphisms on divisor groups (finitely supported $\mathbb Z$-valued functions on places, a place being a proper valuation subring containing $K$, resp. $k$, and a principal ideal ring), and $W\mapsto W|_{\varphi}$, $Y\mapsto Y|_{\bar\varphi}$ for restriction of places (comap of the valuation subring). Let $r_1\colon \mathrm{Place}(K,F_1)\to\mathrm{Place}(k,C_1)$ and $r\colon \mathrm{Place}(K,F_2)\to\mathrm{Place}(k,C_2)$ be arbitrary maps of sets, inducing $\mathbb Z$-linear maps $r_{1*}$, $r_{*}$ on divisors by transport of support. Assume: every place of $F_1/K$, of $F_2/K$, of $C_1/k$ and of $C_2/k$ has residue degree $1$ (the residue field has $K$-, resp. $k$-, rank one); $r_{*}(\varphi^{*}D)=\bar\varphi^{*}(r_{1*}D)$ for every divisor $D$ of $F_1/K$ lying in the kernel of the degree map; $\deg(\varphi^{*}[v])\le \deg(\bar\varphi^{*}[r_1v])$ for every place $v$ of $F_1/K$; and $r_1$ is nowhere constant, in the sense that for every $v$ there is $v'$ with $r_1v'\ne r_1v$. The conclusion is the conjunction of three assertions: $r_{*}(\varphi^{*}D)=\bar\varphi^{*}(r_{1*}D)$ for every divisor $D$ of $F_1/K$, with no degree restriction; $(rW)|_{\bar\varphi}=r_1(W|_{\varphi})$ for every place $W$ of $F_2/K$; and $r_{1*}(\varphi_{*}D)=\bar\varphi_{*}(r_{*}D)$ for every divisor $D$ of $F_2/K$.
--
--   This is the combinatorial core of the functoriality of reduction of divisors along a covering of curves in Deuring's sense: compatibility of a pair of reductions of places with the conorm on degree-zero divisor classes, together with a non-degeneracy of the degrees, upgrades to compatibility for all divisors, to the statement that the reduction of a place lies over the reduction of its restriction, and to compatibility with the norm. It is used in the reduction modulo $\ell$ of Hecke correspondences on modular curves, in [`ModularCurve.reductionModL_heckeOperatorBar_of_ne`](thm.html#ModularCurve.reductionModL_heckeOperatorBar_of_ne) and [`ModularCurve.reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne`](thm.html#ModularCurve.reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
    {K F₁ F₂ : Type*} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
    {k C₁ C₂ : Type*} [Field k] [Field C₁] [Field C₂] [Algebra k C₁] [Algebra k C₂]
    [HasPrincipalDivisors K F₂] [HasPrincipalDivisors k C₂]
    (φ : F₁ →ₐ[K] F₂) (hφ : φ.toRingHom.IsIntegral)
    (φb : C₁ →ₐ[k] C₂) (hφb : φb.toRingHom.IsIntegral)
    (r₁ : Place K F₁ → Place k C₁) (r : Place K F₂ → Place k C₂)
    (h1F₁ : ∀ v : Place K F₁, v.deg = 1) (h1F₂ : ∀ W : Place K F₂, W.deg = 1)
    (h1C₁ : ∀ Q : Place k C₁, Q.deg = 1) (h1C₂ : ∀ Y : Place k C₂, Y.deg = 1)
    (hcompat : ∀ D : Divisor K F₁, D ∈ Divisor.degZero (K := K) (F := F₁) →
      Finsupp.mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (Finsupp.mapDomain r₁ D))
    (hdeg : ∀ v : Place K F₁,
      Divisor.degree (Divisor.pullbackAlong φ hφ (Finsupp.single v 1)) ≤
        Divisor.degree (Divisor.pullbackAlong φb hφb (Finsupp.single (r₁ v) 1)))
    (hnc : ∀ v : Place K F₁, ∃ v' : Place K F₁, r₁ v' ≠ r₁ v) :
    (∀ D : Divisor K F₁, Finsupp.mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (Finsupp.mapDomain r₁ D)) ∧
    (∀ W : Place K F₂, (r W).restrictAlong φb hφb = r₁ (W.restrictAlong φ hφ)) ∧
    (∀ D : Divisor K F₂, Finsupp.mapDomain r₁ (Divisor.pushforwardAlong φ hφ D) =
        Divisor.pushforwardAlong φb hφb (Finsupp.mapDomain r D)) := by sorry
