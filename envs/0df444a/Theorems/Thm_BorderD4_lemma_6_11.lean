-- Prove2me | Theorems.Thm_BorderD4_lemma_6_11
-- name    : BorderD4.lemma_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:16.284564+00:00
-- url     : https://prove2.me/theorems/ecb5a6d9-db2c-424d-b4ce-14414ce87ed6
-- title:
--   Lemma 6.11: a power-series parametrization killing all of $I$
-- statement:
--   Let $I\subseteq F[[\varepsilon]][x]$ be a prime ideal with $\varepsilon\notin I$, let $b\in F^N$ satisfy $g(0,b)=0$ for all $g\in I$, and let $T\subseteq[N]$ with $\dim F((\varepsilon))[x]/IF((\varepsilon))[x]=|T|$; write $u=x_T$, $b_T=(b_i)_{i\in T}$. Suppose every $a\notin T$ has $\tilde Q_a\in I\cap F[[\varepsilon]][u,x_a]$ with:
--
--   1. $\tilde Q_a(0,b_T,x_a)\in F[x_a]$ nonzero;
--   2. $\mathrm{Res}_{x_a}(\tilde Q_a,\partial_{x_a}\tilde Q_a)=\varepsilon^{j_a}R_a$ with $j_a\ge 0$, $R_a\in F[[\varepsilon]][u]$ and $R_a(0,b_T)\ne 0$.
--
--   Then there are $e\ge 1$ and $r_a\in F[[\varepsilon,u]]$ with $r_a(0,0)=0$ such that $\sigma(g)=g(\varepsilon^e,b+(u,r))$ satisfies $I\subseteq\ker\sigma$, and $\sigma(\partial_{x_a}\tilde Q_a)$ is an $\varepsilon$-unit for every $a\notin T$.
--
--   The series satisfy every relation in $I$, not only the individual equations $\tilde Q_a=0$.
--
--   Differences from the source:
--   - generalization: §6 fixes $N=(k+1)n$ (p.49) → an arbitrary finite nonempty index type; reason: the proof uses $N$ only as the number of variables; $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$ is the source
--   - encoding: $\tilde Q_a\in F[[\varepsilon]][u,x_a]$, $R_a\in F[[\varepsilon]][u]$ → elements of $F[[\varepsilon]][x]$ with variables in $T\cup\{a\}$, respectively $T$; reason: these are the same subrings
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.11, p.57

import Mathlib
import Definitions.Def_BorderD4_evalAt
import Definitions.Def_BorderD4_toK
import Definitions.Def_BorderD4_resIn
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- Lemma 6.11, a power-series parametrization: for a prime `I ⊆ F[[ε]][x]` with `ε ∉ I`, a point `b` with `g(0, b) = 0`
for all `g ∈ I`, and `T` with `dim F((ε))[x]/I F((ε))[x] = |T|`, suppose each `a ∉ T` has `Q̃_a ∈ I ∩ F[[ε]][u, x_a]` with
(1) `Q̃_a(0, b_T, x_a) ≠ 0` and (2) `Res_{x_a}(Q̃_a, ∂_{x_a} Q̃_a) = ε^{j_a} R_a` with `R_a ∈ F[[ε]][u]`, `R_a(0, b_T) ≠ 0`.
Then there are `e ≥ 1` and `r_a ∈ F[[ε, u]]` with `r_a(0, 0) = 0` such that `σ(g) = g(ε^e, b + (u, r))` kills all of `I`,
and `σ(∂_{x_a} Q̃_a)` is an ε-unit for every `a ∉ T`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.11, p.57.

**Formalization Note** `I ⊆ ker σ` is for all of `I`, not only the `Q̃_a`, which is the point of the lemma. `R_a` lies in
`F[[ε]][u]` as an element of `F[[ε]][x]` with variables in `T`. -/
theorem lemma_6_11 {F σ : Type*} [Field F] [IsAlgClosed F] [CharZero F] [Fintype σ] [DecidableEq σ]
    [Nonempty σ] (I : Ideal (MvPolynomial σ F⟦X⟧)) [I.IsPrime]
    (hε : MvPolynomial.C PowerSeries.X ∉ I) (b : σ → F) (hb : ∀ g ∈ I, eval b (specialize g) = 0)
    (T : Finset σ)
    (hT : ringKrullDim (MvPolynomial σ (LaurentSeries F) ⧸ I.map (toK (F := F) (σ := σ))) =
      ((T.card : ℕ) : WithBot ℕ∞))
    (Qt : {a // a ∉ T} → MvPolynomial σ F⟦X⟧) (hQI : ∀ a, Qt a ∈ I)
    (hQv : ∀ a, (Qt a).vars ⊆ insert a.1 T) (h1 : ∀ a, fiberAt a.1 b (Qt a) ≠ 0)
    (h2 : ∀ a, ∃ (j : ℕ) (R : MvPolynomial σ F⟦X⟧), R.vars ⊆ T ∧
      resIn a.1 (Qt a) = MvPolynomial.C PowerSeries.X ^ j * R ∧ eval b (specialize R) ≠ 0) :
    ∃ (e : ℕ) (he : e ≠ 0) (r : {a // a ∉ T} → EpsSeries F T),
      (∀ a, MvPowerSeries.constantCoeff (PowerSeries.constantCoeff (r a)) = 0) ∧
      I ≤ RingHom.ker (expandEval T e he (shifted T b r)) ∧
      ∀ a, IsEpsUnit (expandEval T e he (shifted T b r) (pderiv a.1 (Qt a))) := by sorry

end BorderD4
