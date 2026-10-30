-- Prove2me | Theorems.Thm_ErdosStraus242_family_1223
-- name    : ErdosStraus242.family_1223
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-29T23:00:28.100103+00:00
-- url     : https://prove2.me/theorems/db5533c1-d4f8-409e-af18-61eeb21df783
-- title:
--   An explicit Erdős–Straus family modulo 1223
-- statement:
--   Let $p>2$ be prime with $p\equiv-1\pmod{1223}$. Then $4/p$ is the sum of three distinct positive unit fractions. More precisely, putting $k=(p+1)/1223$, the ordered denominators are $306k$, $306p$, and $306pk$. Here $k\ge2$: the exceptional value $k=1$ would give the composite number $p=1222$. The identity follows from $p+1=1223k$ and $1223+1=4\cdot306$. This is an elementary additional congruence family for the existing residual Erdős–Straus target, not a proof of that target. For example, the prime $3461089=1223\cdot2830-1$ satisfies all 135 existing exclusions, so the new family covers inputs left by that sieve.
-- source:
--   Derived here from the displayed explicit witnesses and the identity (p+k+1)/(306pk)=4/p when p+1=1223k; not a quoted theorem or a claim of new mathematics. Context: Bloom–Elsholtz, Egyptian fractions, NAW 5/23 no.4 (2022), pp. 238–239, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf. Intended supporting family for ErdosStraus242.hard_core_840_after_135_sieves (3f9928f7-eca7-4d4e-b849-039d61e45425).

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic

namespace ErdosStraus242
theorem family_1223 (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hmod : p % 1223 = 1222) : IsErdosStraus p := by sorry
end ErdosStraus242
