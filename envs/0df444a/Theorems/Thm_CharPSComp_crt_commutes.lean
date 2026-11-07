-- Prove2me | Theorems.Thm_CharPSComp_crt_commutes
-- name    : CharPSComp.crt_commutes
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:05.453059+00:00
-- url     : https://prove2.me/theorems/60f07858-764b-4cb9-a706-1f22d0aad219
-- title:
--   Proof of Theorem 1 — the projections $\Pi_i$ commute with composition and truncation, and the components add up
-- statement:
--   Let $R$ have characteristic $c\ge2$, with $\epsilon_i$ as in §3.6.3 (for any admissible choice of the $u_i$), and let $\Pi_i$ be the coefficientwise projection $a\mapsto\epsilon_ia$, so $\Pi_i(F)=\epsilon_iF$. For all $f,g\in R[x]$ and $n\ge0$:
--
--   1. $$\big(\Pi_i(f)\circ\Pi_i(g)\big)(x)\bmod x^n=\Pi_i\big(f(g(x))\bmod x^n\big)$$ for every component $i$;
--   2. $\sum_i\Pi_i\big(f(g(x))\bmod x^n\big)=f(g(x))\bmod x^n$.
--
--   So running the prime-power algorithm on each component and adding the results gives $f(g(x))\bmod x^n$ ("The accumulated polynomial is $f(g(x))\bmod x^n$", same page).
--
--   **Formalization Note** $\Pi_i(F)$ is `C ϵ_i * F` in $R[x]$; composition in $(\epsilon_iR)[x]$, whose identity is $\epsilon_i$, agrees with composition in $R[x]$ of the projected polynomials.
--
--   Differences from the source:
--   - encoding: $\Pi_i:R[z]\to(\epsilon_iR)[z]$ and composition over $\epsilon_iR$ → multiplication by the constant $\epsilon_i$ in $R[x]$ and composition in $R[x]$; reason: $(\epsilon_if)\circ(\epsilon_ig)$ computed in $R[x]$ is the composition over $\epsilon_iR$, since $\epsilon_i\cdot(\epsilon_ig)^0=\epsilon_i$
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Proof of Theorem 1, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_CharPSComp_J
import Definitions.Def_CharPSComp_crtIdem

open Polynomial

namespace CharPSComp

/-- Chinese remaindering, the components commute with composition, Zhu, *Faster Power Series
Composition in Fixed Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…),
proof of Theorem 1, p.18 (PDF p.19).

With `ϵ_i` as in §3.6.3 and `Π_i` the coefficientwise projection `a ↦ ϵ_i a` (so
`Π_i(F) = ϵ_i F`), "The coefficient homomorphism Π_i commutes with substitution and truncation.
Hence the call on Π_i(f), Π_i(g) returns (Π_i(f) ∘ Π_i(g))(x) mod xⁿ = Π_i(f(g(x)) mod xⁿ)", and
"The accumulated polynomial is f(g(x)) mod xⁿ": `Σ_i Π_i(f(g(x)) mod xⁿ) = f(g(x)) mod xⁿ`.

**Formalization Note** `Π_i(F)` is `C ϵ_i * F` in `R[x]`; the composition over `ϵ_i R` (whose
identity is `ϵ_i`) agrees with the composition in `R[x]` of the projected polynomials. Components
are indexed by the primes `p ∣ c`. -/
theorem crt_commutes {R : Type*} [CommRing R] (c : ℕ) (hc : 2 ≤ c) [CharP R c] (u : ℕ → ℤ)
    (hu : ∀ p ∈ c.primeFactors,
      (((c / ppart c p : ℕ) : ℤ) * u p) ≡ 1 [ZMOD (ppart c p : ℤ)])
    (f g : R[X]) (n : ℕ) :
    (∀ p ∈ c.primeFactors,
        trunc n ((C (crtIdem R c p (u p)) * f).comp (C (crtIdem R c p (u p)) * g))
          = C (crtIdem R c p (u p)) * trunc n (f.comp g)) ∧
      ∑ p ∈ c.primeFactors, C (crtIdem R c p (u p)) * trunc n (f.comp g) = trunc n (f.comp g) := by sorry

end CharPSComp
