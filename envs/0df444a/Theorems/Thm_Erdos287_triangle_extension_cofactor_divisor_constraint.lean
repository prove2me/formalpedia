-- Prove2me | Theorems.Thm_Erdos287_triangle_extension_cofactor_divisor_constraint
-- name    : Erdos287.triangle_extension_cofactor_divisor_constraint
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:07:36.113081+00:00
-- url     : https://prove2.me/theorems/af9543fe-c46a-46e5-93f8-5faf929e181a
-- title:
--   Divisor constraint for extending a fixed adjacent prime pair to a triangle
-- statement:
--   Suppose $ax-by=\epsilon$, $cx-dz=\sigma$ and $ey-fz=\theta$ with $|\theta|=1$. Assume $(a,b)=(c,d)=(e,f)=1$, $a,b,e>0$, and balance $ead=fcb$. Write $g=\gcd(a,c)$ and $h=\gcd(b,d)$. Then $|(a/g)\sigma-(c/g)\epsilon|=h$. In particular, when the first two differences are signs, fixing the shared cofactors $a,b$, the divisors $g,h$, and the signs leaves at most two possibilities for $c$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.triangle_extension_cofactor_divisor_constraint (a b c d e f : ℕ) (x y z ε η θ : ℤ)
    (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (hab : a.Coprime b) (hcd : c.Coprime d) (hef : e.Coprime f)
    (hbalance : e * (a * d) = f * (c * b))
    (hxy : (a : ℤ) * x - (b : ℤ) * y = ε)
    (hxz : (c : ℤ) * x - (d : ℤ) * z = η)
    (hyz : (e : ℤ) * y - (f : ℤ) * z = θ) (hθ : |θ| = 1) :
    |((a / Nat.gcd a c : ℕ) : ℤ) * η - ((c / Nat.gcd a c : ℕ) : ℤ) * ε|
      = ↑(Nat.gcd b d) := by sorry
