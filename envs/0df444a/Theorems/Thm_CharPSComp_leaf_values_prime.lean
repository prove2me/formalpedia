-- Prove2me | Theorems.Thm_CharPSComp_leaf_values_prime
-- name    : CharPSComp.leaf_values_prime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:55.223822+00:00
-- url     : https://prove2.me/theorems/378ac054-2ae4-47be-89e8-394a473aa7ca
-- title:
--   Leaf values in prime characteristic: $J_{K,t}=f_{K,t}(g_0^K)$
-- statement:
--   Let $R$ be a nonzero commutative ring of prime characteristic $p$, $m,n\ge1$, $f,g\in R[x]$ with $\deg f<m$, $\deg g<n$, $\sigma=\min(m,n)$, $N=p^{\lceil\log_pn\rceil}$ and $K=p^{\lceil\log_p\sigma\rceil}$. For every $0\le t<K$ the leaf answer is the constant
--   $$J_{K,t}=f_{K,t}\big(g_0^K\big),\qquad g_0=[x^0]g,$$
--   viewed as a constant polynomial at precision $N/K$. This holds in both regimes, $m\le n$ (each residue class contains at most one coefficient) and $m>n$ ($K=N$ and $(g(x))^K\equiv g_0^K\pmod{x^N}$).
--
--   The leaves are where the recursion starts; their values are computed by Horner's rule from the input coefficients.
--
--   Differences from the source:
--   - encoding: the scalar $J_{K,t}$ viewed as a constant polynomial at precision $N/K$ → `J … = C (eval …)`; reason: a constant polynomial is its constant term
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §3.1, "Stopping conditions" and "Leaf evaluation by Horner's rule", p.7 (PDF p.8)

import Mathlib
import Definitions.Def_CharPSComp_J

open Polynomial

namespace CharPSComp

/-- Leaf values in prime characteristic, Zhu, *Faster Power Series Composition in Fixed Positive
Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), §3.1, "Stopping conditions"
and "Leaf evaluation by Horner's rule", p.7 (PDF p.8).

In characteristic `p`, with `N = p^{⌈log_p n⌉}` and `K = p^{⌈log_p σ⌉}`, `σ = min(m, n)`, each leaf
returns the scalar `J_{K,t} = f_{K,t}(g₀^K)` for `0 ≤ t < K`, viewed as a constant polynomial at
precision `N/K`; this covers both regimes `m ≤ n` and `m > n`.

**Formalization Note** `g₀ = [x⁰]g`. The statement is one equality for every `t < K`, with no case
split on `m ≤ n`. -/
theorem leaf_values_prime {R : Type*} [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime]
    [CharP R p] (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (f g : R[X]) (hf : f.degree < m)
    (hg : g.degree < n) (t : ℕ) (ht : t < Kpow p m n) :
    J (Npow p n) m (Kpow p m n) t f g
      = C ((strided f m (Kpow p m n) t).eval (g.coeff 0 ^ Kpow p m n)) := by sorry

end CharPSComp
