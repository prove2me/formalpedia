-- Prove2me | Theorems.Thm_ChebotarevDensity_cyclePattern_pow_coprime
-- name    : ChebotarevDensity.cyclePattern_pow_coprime
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T14:26:52.235564+00:00
-- url     : https://prove2.me/theorems/4333dd62-ef59-4f01-9889-b42feaf83184
-- title:
--   Cycle patterns are invariant under coprime powers
-- statement:
--   Let $f\in\mathbb Z[X]$ and let $G=\operatorname{Gal}(f)$ be its Galois group, acting on the zeros of $f$. If $\sigma\in G$ has order $m$ and $k$ is an integer coprime to $m$, then $\sigma$ and $\sigma^k$ have the same cycle pattern (multiset of cycle lengths of the induced permutation of the zeros of $f$):
--   $$\text{cycle pattern of }\sigma^{k}=\text{cycle pattern of }\sigma\qquad(\gcd(k,m)=1).$$
--
--   This is what makes the cycle pattern a function on "rational conjugacy classes", which is the setting of Frobenius's density theorem.
-- source:
--   Stevenhagen–Lenstra, Chebotarëv and his density theorem, Math. Intelligencer 18 (1996), no. 2, pp. 32–34 (Theorem of Frobenius, decomposition types, cycle patterns) and Appendix, pp. 35–36

import Definitions.Def_ChebotarevDensity_Defs
import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField

namespace ChebotarevDensity

theorem cyclePattern_pow_coprime (f : ℤ[X]) (g : GalGroup f) (k : ℕ)
    (hk : Nat.Coprime k (orderOf g)) :
    cyclePattern f (g ^ k) = cyclePattern f g := by sorry

end ChebotarevDensity
