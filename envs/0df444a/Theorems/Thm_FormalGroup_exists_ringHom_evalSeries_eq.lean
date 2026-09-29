-- Prove2me | Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
-- name    : FormalGroup.exists_ringHom_evalSeries_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/d2f8ec31-5fde-566c-9fb1-84dfbc5ee48a
-- title:
--   Adic evaluation of power series as a ring homomorphism
-- statement:
--   Let $T$ be a commutative ring, $I \subseteq T$ an ideal such that $T$ is $I$-adically complete, and let $x \in I$. The assertion is that there is a ring homomorphism $e : T[[X]] \to T$ with two properties. First, for every power series $f \in T[[X]]$ the value $e(f)$ agrees with [`FormalGroup.evalSeries f x`](def/FormalGroup_NSeries.html#L85), that is, with $\mathrm{eval}_2$ of $f$ along the structure map $T \to T$ at the point $x$, formed with respect to the uniformity on the coefficient ring being the discrete one and the uniformity on the target being the $I$-adic uniformity attached to $I$ (the `WithIdeal` structure given by $I$). Second, $e$ restricted to polynomials is ordinary polynomial evaluation: for every $p \in T[X]$, with $p$ regarded as a power series, $e(p) = p(x)$. Thus the possibly only partially defined, topologically given substitution $f \mapsto f(x)$ is realised globally by an honest ring homomorphism on all of $T[[X]]$, extending evaluation of polynomials at $x$.
--
--   This is the bridge between the substitution operation [`FormalGroup.evalSeries`](def/FormalGroup_NSeries.html#L85) used throughout the formal-group vocabulary and the ring-homomorphism property of power-series evaluation, in the case of an $I$-adically complete ring and an argument in $I$. It is used wherever one-variable substitutions into formal group laws and their $n$-series must be manipulated additively and multiplicatively over complete local or adic base rings, and in particular by the statements about Drinfeld bases and law homomorphisms over such rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_ringHom_evalSeries_eq.lean

import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.exists_ringHom_evalSeries_eq
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (x : T) (hx : x ∈ I) :
    ∃ e : PowerSeries T →+* T,
      (∀ f : PowerSeries T, (letI : WithIdeal T := ⟨I⟩; FormalGroup.evalSeries f x) = e f) ∧
      (∀ p : Polynomial T, e (p : PowerSeries T) = p.eval x) := by sorry
