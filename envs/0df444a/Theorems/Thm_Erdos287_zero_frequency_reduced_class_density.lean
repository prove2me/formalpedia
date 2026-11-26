-- Prove2me | Theorems.Thm_Erdos287_zero_frequency_reduced_class_density
-- name    : Erdos287.zero_frequency_reduced_class_density
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T18:21:46.436527+00:00
-- url     : https://prove2.me/theorems/411a3185-f0d9-4ab1-925f-8368ee5542c9
-- title:
--   Normalized zero-frequency density for overlapping moduli
-- statement:
--   For positive moduli $a,b$, put $L=\operatorname{lcm}(a,b)$ and $G=\gcd(a,b)$. Given any reduced class $r$ modulo $a$, let $C_r$ count the units modulo $L$ reducing to $r$. Then $C_r/(L\varphi(b))=1/(L\varphi(G))$.
-- source:
--   Erdős #287, zero-frequency terms in mixed progression dispersion.

import Mathlib

theorem Erdos287.zero_frequency_reduced_class_density (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (r : (ZMod a)ˣ) :
    let L := a.lcm b
    let C := Nat.card {w : (ZMod L)ˣ // ZMod.unitsMap (Nat.dvd_lcm_left a b) w = r}
    (C : ℚ) / ((L : ℚ) * (b.totient : ℚ)) = 1 / ((L : ℚ) * ((a.gcd b).totient : ℚ)) := by sorry
