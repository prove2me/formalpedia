-- Prove2me | Theorems.Thm_CharPSComp_lemma_7
-- name    : CharPSComp.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:48.187286+00:00
-- url     : https://prove2.me/theorems/b913a1a5-67fa-44b2-969a-ce1cec515d42
-- title:
--   Lemma 7 with (8) — lifting the Frobenius congruence: $(a+pb)^\eta=a^\eta$ and $((v(x))^\eta)^k=(\Phi_k(v)(x^k))^\eta$
-- statement:
--   Let $p$ be prime, $e\ge1$ and $\eta\triangleq p^{e-1}$. In any commutative ring $R$ with $p^e\cdot1_R=0_R$:
--
--   1. $(a+pb)^\eta=a^\eta$ for all $a,b\in R$;
--   2. for $k=p^t$, $t\ge0$, and $v\in R[x]$,
--   $$\big((v(x))^\eta\big)^k=\big(\Phi_k(v)(x^k)\big)^\eta, \tag{8}$$
--   where $\Phi_k$ raises each coefficient to its $k$-th power.
--
--   Identity (8) replaces the Frobenius identity $(A(x))^k=\Phi_k(A)(x^k)$ of prime characteristic, so the same recursion runs over rings of characteristic $p^e$.
--
--   **Formalization Note** $\Phi_k(v)(x^k)$ is `expand R k (Phi k v)`. The ring may be the zero ring, as on the page.
--
--   Differences from the source:
--   - encoding: $\Phi_k(v)(x^k)$ → `expand R (p ^ t) (Phi (p ^ t) v)`; reason: substitution of $x^k$ is `expand`
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Lemma 7 with display (8), p.14 (PDF p.15)

import Mathlib
import Definitions.Def_CharPSComp_J

open Polynomial

namespace CharPSComp

/-- Lemma 7 (Lifting the Frobenius congruence) of Zhu, *Faster Power Series Composition in Fixed
Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), p.14 (PDF p.15),
with display (8).

Let `p` be prime, `e ≥ 1` and `η ≜ p^{e−1}`. In any commutative ring `R` with `pᵉ · 1_R = 0_R`,
1. `(a + pb)^η = a^η` for all `a, b ∈ R`;
2. for `k = pᵗ`, `t ≥ 0`, and `v ∈ R[x]`, `((v(x))^η)^k = (Φ_k(v)(xᵏ))^η` (8), where `Φ_k` raises
   each coefficient to its `k`-th power.

**Formalization Note** `Φ_k(v)(xᵏ)` is `expand R k (Phi k v)`. The ring may be the zero ring, as on
the page. -/
theorem lemma_7 {R : Type*} [CommRing R] (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e)
    (hpe : ((p ^ e : ℕ) : R) = 0) :
    (∀ a b : R, (a + (p : R) * b) ^ (p ^ (e - 1)) = a ^ (p ^ (e - 1))) ∧
      ∀ (t : ℕ) (v : R[X]),
        (v ^ (p ^ (e - 1))) ^ (p ^ t) = (expand R (p ^ t) (Phi (p ^ t) v)) ^ (p ^ (e - 1)) := by sorry

end CharPSComp
