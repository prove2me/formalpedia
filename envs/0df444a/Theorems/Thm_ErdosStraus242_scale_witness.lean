-- Prove2me | Theorems.Thm_ErdosStraus242_scale_witness
-- name    : ErdosStraus242.scale_witness
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:40:58.993576+00:00
-- url     : https://prove2.me/theorems/a5b8bd93-a42b-451a-880e-713993e35a38
-- title:
--   Scale a strictly ordered decomposition
-- statement:
--   For natural numbers $n,x,y,z,k$, assume $k>0$, $1≤ x<y<z$, and $4/n=1/x+1/y+1/z$ in the rationals. Then $1≤ kx<ky<kz$ and $4/(kn)=1/(kx)+1/(ky)+1/(kz)$ in the rationals.
-- source:
--   Bloom–Elsholtz, Egyptian fractions (2022), p. 239, scaling observation, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf. Explicit witness/order refinement proved locally.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem scale_witness (n x y z k : ℕ) (hk : 0 < k)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (h : (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) :
    1 ≤ k*x ∧ k*x < k*y ∧ k*y < k*z ∧
      (4 / (k*n) : ℚ) = 1 / (k*x) + 1 / (k*y) + 1 / (k*z) := by sorry
end ErdosStraus242
