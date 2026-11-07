-- Prove2me | Theorems.Thm_AlmostMMS_theorem_3_2
-- name    : AlmostMMS.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:45.938471+00:00
-- url     : https://prove2.me/theorems/4c21bc8d-94f1-47f3-92d0-65b46a70d151
-- title:
--   Theorem 3.2 — head and tail rounding
-- statement:
--   Let $\Pi$ be a shared set of head profiles with $|\pi|\le q$ for an integer $q\ge3$, and let $(x_i,\Pi)$, $i\in N$, be fractional profiles. Suppose that every $\pi\in\Pi-\bot$ has $\Delta(\pi)=0$ or $\Delta(\pi)\ge\delta$, for some $\delta\in(0,1]$. For any $\lambda>1$ there are integer head profiles $(y_i,\Pi)$, with $y_i(\pi)\in\{0,1\}$ and $y_i(\pi)=1$ for $\pi\ne\bot$ only if $x_i(\pi)>0$, such that for all $0\le\ell\le m$
--   $$
--   H(y,\Pi,\ell)\le H(x,\Pi,\ell),\qquad T(y,\Pi,\ell)\le\lambda T(x,\Pi,\ell),
--   $$
--   and
--   $$
--   I(y,\Pi)\ge I(x,\Pi)-\rho(q,\delta,X).
--   $$
--   All head load constraints survive exactly, the tail load constraints are violated by at most the factor $\lambda$, and the number of assigned profiles drops by an amount logarithmic in $X$.
--
--   Differences from the source:
--   - generalization: the ordered instance of §3 → any nonnegative values `v`; reason: the proof in Appendix B uses neither the item order nor the MMS bundles; an ordered instance is a special case
--   - encoding: h_max, T_max as maxima over i ∈ N → `Finset.sup` on ℕ and a real ⨆ over the finite type of agents; reason: they are the maxima; both are 0 when there are no agents, a case with nothing to round
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 3.2, p.25; Theorem B.1, p.51

import Mathlib
import Definitions.Def_AlmostMMS_Q
import Definitions.Def_AlmostMMS_deficit
import Definitions.Def_AlmostMMS_fracH

namespace AlmostMMS

open Finset

/-- **Theorem 3.2 (Head and tail rounding), p.25 (= Theorem B.1, p.51).** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): let `Π` be a shared set
of head profiles with `|π| ≤ q` for an integer `q ≥ 3`, let `(x_i, Π)` be fractional profiles, and suppose
every `π ∈ Π - ⊥` has `Δ(π) = 0` or `Δ(π) ≥ δ` for some `δ ∈ (0, 1]`. For any `λ > 1` there are integer
head profiles `(y_i, Π)` with `y_i(π) ∈ {0, 1}`, `y_i(π) = 1` for `π ≠ ⊥` only if `x_i(π) > 0`, and
`H(y, Π, ℓ) ≤ H(x, Π, ℓ)`, `T(y, Π, ℓ) ≤ λ T(x, Π, ℓ)` for all `0 ≤ ℓ ≤ m`, and
`I(y, Π) ≥ I(x, Π) - ρ(q, δ, X)`.

**Formalization Note.** `y` has the same type as `x`, as printed. The valuation only has to be nonnegative:
the proof uses neither the common item order nor the MMS bundles. The value `ρ(q, δ, X)` is `rhoRound`. -/
theorem theorem_3_2 {n m q : ℕ} (hq : 3 ≤ q) (v : Fin n → Fin m → ℝ) (hv : ∀ i e, 0 ≤ v i e)
    (Ps : Finset (Option (Multiset ℝ))) (hPs : IsProfileSet q Ps)
    (hcard : ∀ p, some p ∈ Ps → p.card ≤ q)
    (x : Fin n → Option (Multiset ℝ) → ℝ) (hx : IsFractionalProfile Ps x)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ p, some p ∈ Ps → deficit q p = 0 ∨ δ ≤ deficit q p)
    (lam : ℝ) (hlam : 1 < lam) :
    ∃ y : Fin n → Option (Multiset ℝ) → ℝ, IsFractionalProfile Ps y ∧
      (∀ i, ∀ π ∈ Ps, y i π = 0 ∨ y i π = 1) ∧
      (∀ i p, some p ∈ Ps → y i (some p) = 1 → 0 < x i (some p)) ∧
      (∀ ℓ ≤ m, fracH v Ps y ℓ ≤ fracH v Ps x ℓ) ∧
      (∀ ℓ ≤ m, fracT v q Ps y ℓ ≤ lam * fracT v q Ps x ℓ) ∧
      fracI Ps x - rhoRound v q Ps x δ lam ≤ fracI Ps y := by sorry

end AlmostMMS
