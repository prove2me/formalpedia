-- Prove2me | Theorems.Thm_DetParamSVP_theorem_3_4_claim_2
-- name    : DetParamSVP.theorem_3_4_claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:49.616209+00:00
-- url     : https://prove2.me/theorems/2bc5eace-25f9-47f4-969e-65058de56ce4
-- title:
--   Theorem 3.4, Claim 2 — where $g\ne0$, the vector of Eq. (8) has $w|_S=u$ and $\|w\|_p^p\le W$
-- statement:
--   Let $p\ge1$, let $q$ be prime, $k\ge2$, $L=k-1$, and let $S=(x_1,\dots,x_m)$ be distinct elements of $\mathbb F_q$. Let $u\in\mathbb Z^m$ be nonzero with $\|u\|_p\le d$, where $d^p\le h$, and let $I$ be the support of $u$ and $g$ the polynomial of Eq. (10). For every $z_1,\dots,z_L,\tau\in\mathbb F_q$ with $g(z_1,\dots,z_L,\tau)\ne0$:
--
--   1. $z_\ell\notin S$ for every $\ell\in[L]$;
--   2. $x_i+\tau\notin S$ for every $i\in I$;
--   3. $z_\ell\ne z_{\ell'}$ for $1\le\ell<\ell'\le L$;
--   4. $z_\ell\ne x_i+\tau$ for every $\ell\in[L]$ and $i\in I$;
--   5. the vector $w$ of Eq. (8) satisfies $w|_S=u$, and
--   6. $\|w\|_p^p\le W$, where $W=k-1+2h$.
--
--   The claim reduces condition (iii) of Definition 3.1 to finding a point of Eq. (9) at which $g$ does not vanish.
--
--   Differences from the source:
--   - encoding: S = (x₁, …, x_m), "∉ S" → an injective map x : Fin m → ZMod q, "not in the range of x"; reason: S is identified with its underlying set (p.19)
--   - encoding: W = k − 1 + 2h → the natural number k − 1 + 2h with k ≥ 2; reason: no truncation occurs
--   - generalization: the setting of Theorem 3.4 (positive m, d, D, h, k, D ≥ 2, D^p < 2k, q with T < q < 2T, distinct y₁, …, y_L, x₁, …, x_m) → only p ≥ 1, q prime, k ≥ 2, x injective, u ≠ 0, ‖u‖_p ≤ d, d^p ≤ h; reason: the claim and its proof use only these; the source setting satisfies them
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.4, Claim 2, p.21 (setting pp.19–21)

import Definitions.Def_DetParamSVP_LpNorm
import Definitions.Def_DetParamSVP_RSConstruction

set_option autoImplicit false

namespace DetParamSVP

open MvPolynomial

/-- **Claim 2 in the proof of Theorem 3.4.** For every `z₁, …, z_L, τ ∈ F_q` with
`g(z₁, …, z_L, τ) ≠ 0` (`g` of Eq. (10)): `z_ℓ ∉ S`, `x_i + τ ∉ S` (`i ∈ I`), `z_ℓ ≠ z_ℓ'`
(`ℓ < ℓ'`) and `z_ℓ ≠ x_i + τ` (`i ∈ I`). Consequently the vector `w` of Eq. (8) satisfies
`w|_S = u` and `‖w‖_p^p ≤ W`, where `W = k − 1 + 2h`.

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.4, Claim 2, p.21, in the setting of pp.19–21: `L = k − 1`,
`S = (x₁, …, x_m)` distinct, `u ∈ ℤ^m` nonzero with `‖u‖_p ≤ d`, `d^p ≤ h`, `I` the support of
`u`.

**Formalization Note.** `S` is the injective map `x : Fin m → F_q`; "`∉ S`" is "not in the range
of `x`". The point is `Fin.snoc z τ` (`Z_ℓ = z_ℓ`, `Y = τ`). `W = k − 1 + 2h` is computed in
`ℕ` with `k ≥ 2`. Only the hypotheses the claim uses are kept (no `D`, no bound on `q`). -/
theorem theorem_3_4_claim_2 (p : ℝ) (hp : 1 ≤ p) (q : ℕ) [Fact q.Prime] (m d h k : ℕ)
    (hk : 2 ≤ k) (x : Fin m → ZMod q) (hx : Function.Injective x) (u : Fin m → ℤ) (hu : u ≠ 0)
    (hud : lpNorm p u ≤ d) (hdh : (d : ℝ) ^ p ≤ h) (z : Fin (k - 1) → ZMod q) (τ : ZMod q)
    (hg : eval (Fin.snoc z τ) (gPoly (k - 1) u x) ≠ 0) :
    (∀ l, z l ∉ Set.range x) ∧ (∀ i ∈ supp u, x i + τ ∉ Set.range x) ∧
      (∀ l l', l < l' → z l ≠ z l') ∧ (∀ l, ∀ i ∈ supp u, z l ≠ x i + τ) ∧
      eq8Vec u x z τ ∘ x = u ∧
      lpPowSum p (eq8Vec u x z τ) ≤ ((k - 1 + 2 * h : ℕ) : ℝ) := by sorry

end DetParamSVP
