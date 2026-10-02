-- Prove2me | Theorems.Thm_ChebotarevDensity_cyclePattern_conj
-- name    : ChebotarevDensity.cyclePattern_conj
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T14:26:42.271322+00:00
-- url     : https://prove2.me/theorems/bb67db22-e9d4-4c04-8777-d6bdb449e5fa
-- title:
--   Cycle patterns are conjugation invariant
-- statement:
--   Let $f\in\mathbb Z[X]$ and let $G=\operatorname{Gal}(f)$ be its Galois group, acting on the zeros of $f$. The cycle pattern of an element $\sigma\in G$ (the multiset of cycle lengths of the permutation it induces on the zeros of $f$, fixed points included) is invariant under conjugation:
--   $$\text{cycle pattern of }x\sigma x^{-1}=\text{cycle pattern of }\sigma\qquad(\sigma,x\in G).$$
--
--   Consequently the cycle pattern is a well-defined invariant of a conjugacy class of $G$.
-- source:
--   Stevenhagen–Lenstra, Chebotarëv and his density theorem, Math. Intelligencer 18 (1996), no. 2, pp. 32–34 (Theorem of Frobenius, decomposition types, cycle patterns) and Appendix, pp. 35–36

import Definitions.Def_ChebotarevDensity_Defs
import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField

namespace ChebotarevDensity

theorem cyclePattern_conj (f : ℤ[X]) (g x : GalGroup f) :
    cyclePattern f (x * g * x⁻¹) = cyclePattern f g := by sorry

end ChebotarevDensity
