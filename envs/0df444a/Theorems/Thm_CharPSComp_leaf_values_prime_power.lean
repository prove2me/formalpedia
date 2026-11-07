-- Prove2me | Theorems.Thm_CharPSComp_leaf_values_prime_power
-- name    : CharPSComp.leaf_values_prime_power
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:03.34111+00:00
-- url     : https://prove2.me/theorems/8f0c0a1b-2d90-4474-b863-034feb0c94eb
-- title:
--   Leaf values in prime-power characteristic: $J^{(\alpha)}_{K,t}=\sum_if_{\alpha+\eta(t+Ki)}(g_0^{\eta K})^i$
-- statement:
--   Let $R$ be a nonzero commutative ring of characteristic $p^e$, $e\ge1$, $\eta=p^{e-1}$, $m,n\ge1$, $f,g\in R[x]$ with $\deg f<m$, $\deg g<n$, $N=p^{\lceil\log_pn\rceil}$ and $K=p^a=p^{\lceil\log_p\sigma\rceil}$. In both regimes $m\le n$ and $m>n$, the leaf at index $t$ of tree $\alpha$ is the constant
--   $$J^{(\alpha)}_{K,t}=\sum_{i\ge0,\ \alpha+\eta(t+Ki)<m}f_{\alpha+\eta(t+Ki)}\,\big(g_0^{\eta K}\big)^i\qquad(0\le\alpha<\eta,\ 0\le t<K).$$
--
--   These are the starting values of the $\eta$ trees of Algorithm 3.
--
--   **Formalization Note** The sum is $f_{\eta K,\alpha+\eta t}$ evaluated at $g_0^{\eta K}$; $J^{(\alpha)}_{w,t}$ is `Jpe` at $w=p^a=K$.
--
--   Differences from the source:
--   - encoding: the leaf value, a scalar → `Jpe … = C (eval …)`, a constant polynomial; reason: a constant polynomial is its constant term
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §3.6.1, "Leaf values", p.15 (PDF p.16)

import Mathlib
import Definitions.Def_CharPSComp_J

open Polynomial

namespace CharPSComp

/-- Leaf values in prime-power characteristic, Zhu, *Faster Power Series Composition in Fixed
Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), §3.6.1, "Leaf
values", p.15 (PDF p.16).

Let `R` have characteristic `pᵉ`, `e ≥ 1`, `η = p^{e−1}`, `N = p^{⌈log_p n⌉}`,
`K = p^a = p^{⌈log_p σ⌉}`. In both cases `m ≤ n` and `m > n`, the leaf at index `t` of tree `α` has
value
`J^{(α)}_{K,t} = Σ_{i ≥ 0, α+η(t+Ki) < m} f_{α+η(t+Ki)} (g₀^{ηK})ⁱ` for `0 ≤ α < η`, `0 ≤ t < K`,
a constant polynomial.

**Formalization Note** The sum is `f_{ηK, α+ηt}` evaluated at `g₀^{ηK}`; `J^{(α)}_{w,t}` is
`Jpe N m p η j α t` with `w = pʲ` (`Def_CharPSComp_J`), here at `j = a`. -/
theorem leaf_values_prime_power {R : Type*} [CommRing R] [Nontrivial R] (p e : ℕ) [Fact p.Prime]
    (he : 1 ≤ e) [CharP R (p ^ e)] (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (f g : R[X])
    (hf : f.degree < m) (hg : g.degree < n) (α t : ℕ) (hα : α < p ^ (e - 1))
    (ht : t < Kpow p m n) :
    Jpe (Npow p n) m p (p ^ (e - 1)) (Nat.clog p (min m n)) α t f g
      = C ((strided f m (p ^ (e - 1) * Kpow p m n) (α + p ^ (e - 1) * t)).eval
          (g.coeff 0 ^ (p ^ (e - 1) * Kpow p m n))) := by sorry

end CharPSComp
