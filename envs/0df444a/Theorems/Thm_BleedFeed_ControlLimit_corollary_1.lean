-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_corollary_1
-- name    : BleedFeed.ControlLimit.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:03.272987+00:00
-- url     : https://prove2.me/theorems/065fe73a-3f9d-4ee7-9908-1108125fab85
-- title:
--   Corollary 1, p. 17 — under Conditions (4), (5) and Assumption 1, a three-way control limit in age, growth rate and bleed–feed count
-- statement:
--   In the bleed–feed model (see the definition file), assume Condition (4), Condition (5) (on the range $\tilde\imath_{\mu^+}<i<I$) and Assumption 1. Then the optimal bleed–feed decision has a **three-way control-limit structure**:
--
--   1. for every $\mu\in\mathcal M$ and $n\in\{0,\dots,N\}$ there is an integer $i^*(\mu,n)$ such that for all ages $i<I$, continuing is optimal if $i\le i^*(\mu,n)$ and bleed–feed is optimal if $i>i^*(\mu,n)$;
--   2. for every age $i<I$ and $n\in\{0,\dots,N\}$ there is a real $\mu^*(i,n)$ such that for all $\mu\in\mathcal M$, continuing is optimal if $\mu<\mu^*(i,n)$ and bleed–feed is optimal if $\mu>\mu^*(i,n)$;
--   3. for every age $i<I$ and $\mu\in\mathcal M$ there is an integer $n^*(i,\mu)$ such that for all $n\in\{0,\dots,N\}$, bleed–feed is optimal if $n\le n^*(i,\mu)$ and continuing is optimal if $n>n^*(i,\mu)$.
--
--   Here "bleed–feed is optimal in $(i,\mu,n)$" means $n<N$ and $C(i,\mu,n)\le B(n)$, and "continuing is optimal" means $B(n)\le C(i,\mu,n)$, the two branches of the optimality equation
--   $$
--   v(i,\mu,n)=\max\bigl\{C(i,\mu,n),\,B(n)\bigr\}.
--   $$
--
--   This is the paper's headline structural result: an optimal bleed–feed policy is described by three monotone thresholds, which is what makes it implementable on the production floor.
--
--   **Formalization Note** (a) The corollary says only "a threshold above which"; Theorems 1–3, which it summarises, and the definition of a control limit in §1 (p. 5) also say what is optimal below, and both sides are stated. (b) Assumption 1 is added: it is the standing assumption of §4.2 on which Theorem 2 rests. (c) Condition (5) is on the corrected range $\tilde\imath_{\mu^+}<i<I$; the printed range fails for every $\mu<\mu^+$ when $\tilde\imath_{\mu^+}\ge 1$, which would make the corollary vacuous for every nondegenerate $\mathcal M$. (d) The growth-rate threshold is strict on both sides, because the non-strict form can fail at the threshold point when $\nu$ jumps. (e) The integer thresholds may equal $-1$.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 17, Corollary 1 (with Theorems 1–3, pp. 14–16, and Assumption 1, p. 15)

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Corollary 1, p. 17: if Conditions (4) and (5) hold (the latter on the range ĩ_{µ⁺} < i < I),
and Assumption 1 holds, the optimal bleed–feed decision has a three-way control-limit structure:
an age threshold i*(µ, n), a growth-rate threshold µ*(i, n) and a count threshold n*(i, µ), with
bleed–feed optimal above the first two and continuing optimal above the third. -/
theorem corollary_1 (P : Params) (hS : P.Standing)
    (h4 : Condition4 P) (h5 : Condition5 P) (hA1 : Assumption1 P) :
    (∀ μ ∈ P.rates, ∀ n ≤ P.N, ∃ iStar : ℤ, ∀ i < P.I,
        ((i : ℤ) ≤ iStar → ContOpt P i μ n) ∧ (iStar < i → BleedOpt P i μ n)) ∧
    (∀ i < P.I, ∀ n ≤ P.N, ∃ μStar : ℝ, ∀ μ ∈ P.rates,
        (μ < μStar → ContOpt P i μ n) ∧ (μStar < μ → BleedOpt P i μ n)) ∧
    (∀ i < P.I, ∀ μ ∈ P.rates, ∃ nStar : ℤ, ∀ n ≤ P.N,
        ((n : ℤ) ≤ nStar → BleedOpt P i μ n) ∧ (nStar < n → ContOpt P i μ n)) := by sorry

end BleedFeed.ControlLimit
