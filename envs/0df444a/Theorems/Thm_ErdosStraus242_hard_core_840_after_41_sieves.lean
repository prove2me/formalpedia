-- Prove2me | Theorems.Thm_ErdosStraus242_hard_core_840_after_41_sieves
-- name    : ErdosStraus242.hard_core_840_after_41_sieves
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T06:12:18.337477+00:00
-- url     : https://prove2.me/theorems/04000cb4-5d58-4619-9f06-9d4cc4189a01
-- title:
--   Remaining modulo-840 prime cases after the forty-one congruence families
-- statement:
--   Let $p>2$ be prime. Assume $p\bmod 840\in\{1,121,169,289,361,529\}$ and that $p$ avoids the excluded residue classes modulo each of the 41 listed moduli: 11, 19, 23, 31, 43, 47, 59, 71, 79, 83, 107, 131, 139, 143, 151, 163, 167, 179, 191, 199, 211, 223, 227, 239, 251, 263, 271, 283, 307, 311, 331, 347, 359, 367, 379, 383, 419, 431, 439, 443, 467. The remaining assertion is that there are natural numbers $1\le x<y<z$ with $4/p=1/x+1/y+1/z$ in $\mathbb Q$. This is the open residual frontier of Erdős Problem 242, obtained from `ErdosStraus242.hard_core_840_after_39_sieves` by removing the five-class modulo-79 family `ErdosStraus242.family_mod79` and the eight-class modulo-143 family `ErdosStraus242.family_mod143`. It is not claimed as a theorem of the cited survey nor as a proof of the conjecture; together with the two proved families it recovers the previous frontier. The strict denominator convention is retained.
-- source:
--   Erdős Problem 242, https://www.erdosproblems.com/242, restricted from the mission frontier ErdosStraus242.hard_core_840_after_39_sieves. The two additional exclusions come from the modulo-79 and modulo-143 classes of the Bloom–Elsholtz $a=1$ parametrization, p. 239, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf. This residual formulation is a decomposition made here, not a quoted result.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem hard_core_840_after_41_sieves (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hres : p % 840 ∈ ({1, 121, 169, 289, 361, 529} : Finset ℕ))
    (h11 : p % 11 ∉ ({7, 8, 10} : Finset ℕ))
    (h19 : p % 19 ∉ ({14, 15, 18} : Finset ℕ))
    (h23 : p % 23 ∉ ({7, 10, 11, 15, 17, 19, 20, 21, 22} : Finset ℕ))
    (h31 : p % 31 ∉ ({23, 27} : Finset ℕ))
    (h43 : p % 43 ∉ ({39} : Finset ℕ))
    (h47 : p % 47 ∉ ({35} : Finset ℕ))
    (h59 : p % 59 ∉ ({47} : Finset ℕ))
    (h71 : p % 71 ∉ ({59} : Finset ℕ))
    (h79 : p % 79 ∉ ({39, 59, 63, 71, 75} : Finset ℕ))
    (h83 : p % 83 ∉ ({55} : Finset ℕ))
    (h107 : p % 107 ∉ ({71} : Finset ℕ))
    (h131 : p % 131 ∉ ({119} : Finset ℕ))
    (h139 : p % 139 ∉ ({111} : Finset ℕ))
    (h143 : p % 143 ∉ ({71, 95, 107, 119, 127, 131, 135, 139} : Finset ℕ))
    (h151 : p % 151 ∉ ({143} : Finset ℕ))
    (h163 : p % 163 ∉ ({159} : Finset ℕ))
    (h167 : p % 167 ∉ ({163} : Finset ℕ))
    (h179 : p % 179 ∉ ({119} : Finset ℕ))
    (h191 : p % 191 ∉ ({127} : Finset ℕ))
    (h199 : p % 199 ∉ ({179} : Finset ℕ))
    (h211 : p % 211 ∉ ({207} : Finset ℕ))
    (h223 : p % 223 ∉ ({215} : Finset ℕ))
    (h227 : p % 227 ∉ ({151} : Finset ℕ))
    (h239 : p % 239 ∉ ({231} : Finset ℕ))
    (h251 : p % 251 ∉ ({167} : Finset ℕ))
    (h263 : p % 263 ∉ ({255} : Finset ℕ))
    (h271 : p % 271 ∉ ({267} : Finset ℕ))
    (h283 : p % 283 ∉ ({279} : Finset ℕ))
    (h307 : p % 307 ∉ ({263} : Finset ℕ))
    (h311 : p % 311 ∉ ({259} : Finset ℕ))
    (h331 : p % 331 ∉ ({327} : Finset ℕ))
    (h347 : p % 347 ∉ ({335} : Finset ℕ))
    (h359 : p % 359 ∉ ({323} : Finset ℕ))
    (h367 : p % 367 ∉ ({363} : Finset ℕ))
    (h379 : p % 379 ∉ ({303} : Finset ℕ))
    (h383 : p % 383 ∉ ({311} : Finset ℕ))
    (h419 : p % 419 ∉ ({391} : Finset ℕ))
    (h431 : p % 431 ∉ ({407} : Finset ℕ))
    (h439 : p % 439 ∉ ({419} : Finset ℕ))
    (h443 : p % 443 ∉ ({431} : Finset ℕ))
    (h467 : p % 467 ∉ ({463} : Finset ℕ))
    : IsErdosStraus p := by sorry
end ErdosStraus242
