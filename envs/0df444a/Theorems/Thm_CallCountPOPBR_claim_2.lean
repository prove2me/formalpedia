-- Prove2me | Theorems.Thm_CallCountPOPBR_claim_2
-- name    : CallCountPOPBR.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:19.143246+00:00
-- url     : https://prove2.me/theorems/aa5e3ab0-9620-4f2e-adac-9b0358660b94
-- title:
--   Claim 2 — the carry lemma
-- statement:
--   Let $q_1,q_2,q_3,R$ be natural numbers with gaps $q_1-q_2\ge 2R+2$ and $q_2-q_3\ge 2R+2$, and let $u,v$ be positive integers with
--   $$
--   u+v=2^{q_1}+2^{q_2}+2^{q_3},\qquad \mathrm{wt}(u)+\mathrm{wt}(v)\le R.
--   $$
--   Put $W_q=[q-R,q]$. Then:
--
--   1. every set bit of $u$ and of $v$ lies in $W_{q_1}\cup W_{q_2}\cup W_{q_3}$;
--   2. for each $q\in\{q_1,q_2,q_3\}$, the part of $u$ in $W_q$ plus the part of $v$ in $W_q$ equals $2^q$;
--   3. in particular, for each $q\in\{q_1,q_2,q_3\}$, $u$ or $v$ has a set bit in $W_q$.
--
--   The lemma controls how a sum of three widely separated powers of two can split into two integers of low weight.
--
--   Differences from the source:
--   - encoding: q_1 > q_2 > q_3 and gaps q_1 − q_2, q_2 − q_3 ≥ 2R + 2 → q₂ + 2R + 2 ≤ q₁ and q₃ + 2R + 2 ≤ q₂; reason: on natural numbers the gap inequalities are written without subtraction and imply q₁ > q₂ > q₃
--   - encoding: W_q = [q − R, q] → the window [q − R, q] with truncated subtraction; the part of x in W_q is ∑_{i ∈ [q − R, q]} x_i 2^i; reason: bit positions are natural numbers; when q < R the window is [0, q]
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), proof of Theorem 2.8, Claim 2, p.6

import Definitions.Def_CallCountPOPBR_wt
import Definitions.Def_CallCountPOPBR_part

set_option autoImplicit false

namespace CallCountPOPBR

/-- **Claim 2 (carry lemma).** Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), proof of Theorem 2.8, Claim 2, p.6: "Let
t = 2^{q_1} + 2^{q_2} + 2^{q_3} with q_1 > q_2 > q_3 and gaps q_1 − q_2, q_2 − q_3 ≥ 2R + 2, and let
u + v = t with positive integers u, v and wt(u) + wt(v) ≤ R. Put W_q = [q − R, q]. Then (a) every
set bit of u and of v lies in W_{q_1} ∪ W_{q_2} ∪ W_{q_3}, and (b) for each q ∈ {q_1, q_2, q_3}, the
part of u in W_q plus the part of v in W_q equals 2^q; in particular u or v has a set bit in W_q."

**Formalization Note.** `q_1 > q_2 > q_3` follows from the gap hypotheses. The part of `x` in
`W_q` is `part R q x`; the window `[q − R, q]` uses truncated subtraction. -/
theorem claim_2 (q₁ q₂ q₃ R u v : ℕ) (h₁₂ : q₂ + 2 * R + 2 ≤ q₁) (h₂₃ : q₃ + 2 * R + 2 ≤ q₂)
    (hu : 0 < u) (hv : 0 < v) (huv : u + v = 2 ^ q₁ + 2 ^ q₂ + 2 ^ q₃)
    (hwt : wt u + wt v ≤ R) :
    (∀ i, (u.testBit i = true ∨ v.testBit i = true) →
      ∃ q ∈ ({q₁, q₂, q₃} : Finset ℕ), q ≤ i + R ∧ i ≤ q) ∧
    (∀ q ∈ ({q₁, q₂, q₃} : Finset ℕ), part R q u + part R q v = 2 ^ q) ∧
    (∀ q ∈ ({q₁, q₂, q₃} : Finset ℕ),
      ∃ i, q ≤ i + R ∧ i ≤ q ∧ (u.testBit i = true ∨ v.testBit i = true)) := by sorry

end CallCountPOPBR
