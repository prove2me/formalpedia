-- Prove2me | Theorems.Thm_DynHaussler_eq_112
-- name    : DynHaussler.eq_112
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:07.76218+00:00
-- url     : https://prove2.me/theorems/d9946304-6b56-4777-a9d1-c17b01c9ffbf
-- title:
--   Eq. (112) — $\rho_{p,L}(h[x_{1:L}],h'[x_{1:L}])^p\ge2(q-1)/q^2$ for distinct hyperplanes
-- statement:
--   Let $\mathbb F_q$ be a field with $q$ elements and $d\ge1$. List all points of $\mathbb F_q^d$ once, in any fixed order, as $x_1,\dots,x_L$ with $L=q^d$. Then for all distinct $h,h'\in H_q$ and every $1\le p<\infty$,
--   $$
--   \rho_{p,L}\bigl(h[x_{1:L}],h'[x_{1:L}]\bigr)^p\ge\frac{2(q-1)}{q^2}. \tag{112}
--   $$
--
--   With the choice of field size (113) this separates distinct hyperplane traces by more than $2\varepsilon$, which is the packing behind Theorem 6.
--
--   **Formalization Note** The listing is a bijection between $\{0,\dots,L-1\}$ and $\mathbb F_q^d$; the power is a real power.
--
--   Differences from the source:
--   - encoding: a listing x_1, …, x_L of all points once → a bijection e : Fin L ≃ (Fin d → F); reason: 0-based listing; forces L = q^d
--   - encoding: a prime power q ≥ 2 and a field F_q with q elements → any finite field F, q = card F; reason: the cardinality of a finite field is a prime power ≥ 2, and every prime power is one
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (112), p.47 (PDF p.49); listing, Section 9.2, p.47

import Mathlib
import Definitions.Def_DynHaussler_hypClass
import Definitions.Def_DynHaussler_rho

set_option autoImplicit false

namespace DynHaussler

/-- **Eq. (112) (fixed-sequence packing of hyperplanes).** Let `F_q` be a field with `q` elements and
`d ≥ 1`. List all points of `F_q^d` once, in any fixed order, as `x_1, …, x_L` (`L = q^d`). Then for all
distinct `h, h' ∈ H_q` and every `1 ≤ p < ∞`,
`ρ_{p,L}(h[x_{1:L}], h'[x_{1:L}])^p ≥ 2(q − 1)/q^2`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (112), p.47 (PDF p.49); the listing, Section 9.2, p.47.

**Formalization Note** `F` is any finite field and `q = Fintype.card F`. A listing of all points
once is a bijection `e : Fin L ≃ (Fin d → F)` (which forces `L = q^d`); rounds are 0-based. The
power `ρ^p` is `Real.rpow`. -/
theorem eq_112 (F : Type*) [Field F] [Fintype F] (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p)
    (L : ℕ) (e : Fin L ≃ (Fin d → F)) (h h' : (Fin d → F) → ℝ) (hh : h ∈ hypClass F d)
    (hh' : h' ∈ hypClass F d) (hne : h ≠ h') :
    2 * ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ) ^ 2 ≤
      rho p (fun t => h (e t)) (fun t => h' (e t)) ^ p := by sorry

end DynHaussler
