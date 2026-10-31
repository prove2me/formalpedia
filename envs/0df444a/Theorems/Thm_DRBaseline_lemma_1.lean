-- Prove2me | Theorems.Thm_DRBaseline_lemma_1
-- name    : DRBaseline.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:42:26.372262+00:00
-- url     : https://prove2.me/theorems/88aa7213-582d-448e-a9e2-90af21f2ffb8
-- title:
--   Lemma 1: overestimation iff demand is below the baseline
-- statement:
--   Let $\Omega>0$, $c_s>0$, $b\ge0$, $r\ge0$ and $\omega\in[0,2\Omega]$, and let $x$ be any solution of the customer's problem $\max_{s\le\omega}C_c(s)$. Then
--
--   1. if $\omega<b$, the estimated reduction exceeds the actual one: $S(x)>x$;
--   2. if $\omega\ge b$, it does not: $S(x)\le x$.
--
--   So the baseline decides whether the firm over- or under-credits the customer, and by how much ($b-\omega$ or $\omega-b$).
--
--   Differences from the source:
--
--   - encoding: s∗ = arg max, a single function → every solution of the customer's problem (IsCustomerOptimal); reason: the arg max has ties at up to two ω per (b, r); any two selections differ on a null set, so every integral is the paper's
--   - encoding: a given baseline b, rebate r, demand ω → b ≥ 0, r ≥ 0, ω ∈ [0, 2Ω]; reason: the firm's domain and the support of f (p.7)
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Lemma 1, p.13; proof p.OA1

import Mathlib
import Definitions.Def_DRBaseline_IsCustomerOptimal

namespace DRBaseline

/-- **Lemma 1: over- and underestimation of the demand reduction.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Lemma 1, p.13; proof p.OA1.

For a baseline `b ≥ 0`, a rebate `r ≥ 0`, a demand realization `ω ∈ [0, 2Ω]` and any solution
`x` of the customer's problem: if `ω < b` then `S(x) > x`; otherwise `S(x) ≤ x`.

**Formalization Note** `S(x) = (b − (ω − x))⁺` is `estReduction b ω x`; the statement holds for
every maximizer, since `s*` can have ties. -/
theorem lemma_1 (Ω cs b r ω x : ℝ) (hΩ : 0 < Ω) (hcs : 0 < cs) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hω0 : 0 ≤ ω) (hω2 : ω ≤ 2 * Ω) (hx : IsCustomerOptimal cs b r ω x) :
    (ω < b → x < estReduction b ω x) ∧ (b ≤ ω → estReduction b ω x ≤ x) := by sorry

end DRBaseline
