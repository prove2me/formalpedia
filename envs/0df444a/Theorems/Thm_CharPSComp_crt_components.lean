-- Prove2me | Theorems.Thm_CharPSComp_crt_components
-- name    : CharPSComp.crt_components
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:01.026069+00:00
-- url     : https://prove2.me/theorems/06312d8c-da8a-431b-a894-d06b26d5c2a6
-- title:
--   §3.6.3 — the Chinese-remainder idempotents: $\sum\epsilon_i=1$, $\epsilon_i^2=\epsilon_i$, $\epsilon_i\epsilon_j=0$, $\operatorname{char}\epsilon_iR=c_i$
-- statement:
--   Let $R$ be a commutative ring of characteristic $c\ge2$ and factor $c=\prod_ic_i$ into the prime powers $c_i=p_i^{e_i}$. For $d_i\triangleq c/c_i$ choose any integers $u_i$ with $d_iu_i\equiv1\pmod{c_i}$ and put $\epsilon_i\triangleq(d_iu_i)\cdot1_R$. Then
--
--   1. $d_iu_i\equiv0\pmod{c_j}$ for every $j\ne i$;
--   2. $\sum_i\epsilon_i=1_R$, $\epsilon_i^2=\epsilon_i$, and $\epsilon_i\epsilon_j=0$ for $i\ne j$;
--   3. $\epsilon_i$ is the identity of $\epsilon_iR$: $\epsilon_i(\epsilon_ia)=\epsilon_ia$ for all $a\in R$;
--   4. for every integer $s$, $s\epsilon_i=0_R$ exactly when $c_i\mid s$, so $\epsilon_iR$ has characteristic $c_i$.
--
--   These are the components on which Algorithm 4 runs the prime-power algorithm.
--
--   **Formalization Note** Components are indexed by the primes $p\mid c$, with $c_p=p^{v_p(c)}$ (`ppart`).
--
--   Differences from the source:
--   - encoding: components $i\in[r]$ of the factorization $c=\prod_{i=1}^rc_i$ → components indexed by $p\in$ `c.primeFactors` with $c_p=p^{v_p(c)}$; reason: the same factorization
--   - encoding: "$\epsilon_iR$ has identity $\epsilon_i$"; "its characteristic is $c_i$" → $\epsilon_i(\epsilon_ia)=\epsilon_ia$; $s\epsilon_i=0\iff c_i\mid s$; reason: the page's own justification of both claims
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §3.6.3, first paragraph, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_CharPSComp_crtIdem

namespace CharPSComp

/-- Chinese remaindering, the component idempotents, Zhu, *Faster Power Series Composition in
Fixed Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), §3.6.3, p.17
(PDF p.18).

Let `R` have characteristic `c ≥ 2` and factor `c = Π_i c_i` into pairwise coprime prime powers
`c_i = p_i^{e_i}`. For `d_i ≜ c/c_i` choose integers `u_i` with `d_i u_i ≡ 1 (mod c_i)` and put
`ϵ_i ≜ (d_i u_i) · 1_R`. Then
1. the defining integer `d_i u_i` is `0` modulo every other `c_j`;
2. `Σ_i ϵ_i = 1_R`, `ϵ_i² = ϵ_i`, and `ϵ_i ϵ_j = 0` for `i ≠ j`;
3. `ϵ_i` is the identity of `ϵ_i R`: `ϵ_i (ϵ_i a) = ϵ_i a` for every `a ∈ R`;
4. for every integer `s`, `s ϵ_i = 0_R` exactly when `c_i ∣ s` (so `ϵ_i R` has characteristic
   `c_i`).

**Formalization Note** Components are indexed by the primes `p ∣ c` (`c.primeFactors`), with
`c_p = p^{v_p(c)}` (`ppart`); `u p` is the chosen integer, any choice satisfying the congruence. -/
theorem crt_components {R : Type*} [CommRing R] (c : ℕ) (hc : 2 ≤ c) [CharP R c] (u : ℕ → ℤ)
    (hu : ∀ p ∈ c.primeFactors,
      (((c / ppart c p : ℕ) : ℤ) * u p) ≡ 1 [ZMOD (ppart c p : ℤ)]) :
    (∀ p ∈ c.primeFactors, ∀ p' ∈ c.primeFactors, p ≠ p' →
        (ppart c p' : ℤ) ∣ ((c / ppart c p : ℕ) : ℤ) * u p) ∧
      ∑ p ∈ c.primeFactors, crtIdem R c p (u p) = 1 ∧
      (∀ p ∈ c.primeFactors, crtIdem R c p (u p) ^ 2 = crtIdem R c p (u p)) ∧
      (∀ p ∈ c.primeFactors, ∀ p' ∈ c.primeFactors, p ≠ p' →
        crtIdem R c p (u p) * crtIdem R c p' (u p') = 0) ∧
      (∀ p ∈ c.primeFactors, ∀ a : R,
        crtIdem R c p (u p) * (crtIdem R c p (u p) * a) = crtIdem R c p (u p) * a) ∧
      (∀ p ∈ c.primeFactors, ∀ s : ℤ,
        (s : R) * crtIdem R c p (u p) = 0 ↔ (ppart c p : ℤ) ∣ s) := by sorry

end CharPSComp
