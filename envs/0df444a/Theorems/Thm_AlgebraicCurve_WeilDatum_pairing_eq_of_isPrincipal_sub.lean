-- Prove2me | Theorems.Thm_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub
-- name    : AlgebraicCurve.WeilDatum.pairing_eq_of_isPrincipal_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/50a5f05c-c7b3-5afb-b8cf-01d6275c4842
-- title:
--   Invariance of the Weil datum pairing under linear equivalence
-- statement:
--   Let $K$ be a field and $F$ a field extension of $K$ (an algebra over $K$), let $n$ be a nonzero natural number, and assume `HasPrincipalDivisors K F`: every nonzero $f \in F$ has a finitely supported divisor $v \mapsto \operatorname{ord}_v f$ on the places of $F/K$, of degree $0$. Three global hypotheses are imposed: `hrec`, Weil reciprocity, i.e. for nonzero $f, g$ with divisors $D_f, D_g$ whose supports consist of rational places and with $\operatorname{ord}_v f = 0$ or $\operatorname{ord}_v g = 0$ at every $v$, one has $f\langle D_g\rangle = g\langle D_f\rangle$ for the evaluation pairing `Divisor.evalFun`; `hconst`, that every nonzero $u \in F$ with $\operatorname{ord}_v u = 0$ at all places lies in $\operatorname{algebraMap} K F$; and `hmove`, that for every $n$-torsion class $x$ of $\operatorname{Pic}^0(F/K)$ and every finite set $S$ of places there is a degree-zero divisor $D$ representing $x$ all of whose support places are rational (the map $K \to$ residue field is surjective, equivalently $\deg v = 1$) and lie outside $S$. Let $d, d'$ be Weil data of order $n$, each consisting of divisors $D_1, D_2$, nonzero $f_1, f_2$ with $\operatorname{ord}_v f_i = n\,D_i(v)$ for all $v$, with $D_1(v) = 0$ or $D_2(v) = 0$ at every $v$, and with $v$ rational whenever $D_1(v) \neq 0$ or $D_2(v) \neq 0$. If $d'.D_1 - d.D_1$ and $d'.D_2 - d.D_2$ are both principal, i.e. each is the divisor of a nonzero element of $F$, then the two pairing values $f_1\langle D_2\rangle / f_2\langle D_1\rangle \in K$ attached to $d$ and to $d'$ coincide.
--
--   This is the well-definedness of the divisorial Weil pairing: its value depends only on the pair of divisor classes, not on the chosen divisors and witness functions, the change of representative being controlled by Weil reciprocity together with the constants and moving hypotheses. It is used to construct the pairing as a map on $n$-torsion classes of $\operatorname{Pic}^0(F/K)$, in [`AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing`](thm.html#AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_WeilDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.WeilDatum.pairing_eq_of_isPrincipal_sub {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S))
    (d d' : WeilDatum K F n)
    (hL : Divisor.IsPrincipal (d'.D₁ - d.D₁)) (hR : Divisor.IsPrincipal (d'.D₂ - d.D₂)) :
    d'.pairing = d.pairing := by sorry
