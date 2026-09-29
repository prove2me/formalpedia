-- Prove2me | Theorems.Thm_FCP_Kakeya_kakeya_finite_field
-- name    : FCP.Kakeya.kakeya_finite_field
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:51:07.384657+00:00
-- url     : https://prove2.me/theorems/448b0e69-57fd-4028-ab8b-07964b7b3c5b
-- title:
--   Finite field Kakeya bound (Dvir; Bukh--Chao)
-- statement:
--   **Finite-field Kakeya bound.** If $K \subseteq \mathbb{F}_q^{\,n}$ contains a full line in every nonzero direction, then
--   $$|K| \;\ge\; \frac{q^{n}}{(2 - 1/q)^{\,n-1}}.$$
--   Dvir's polynomial method gave the first bound of the form $c_n q^n$; the constant above is the sharp density bound of Bukh and Chao (2021). The dimension is assumed positive: for $n = 0$ the empty set would be a Kakeya set and the bound would read $1 \le 0$.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Kakeya.lean); Z. Dvir, On the size of Kakeya sets in finite fields, J. Amer. Math. Soc. 22 (2009), 1093--1097; B. Bukh and T.-W. Chao, Sharp density bounds on the finite field Kakeya problem, Discrete Analysis 26 (2021)

import Mathlib
import Definitions.Def_FCP_Kakeya

namespace FCP.Kakeya

theorem kakeya_finite_field (F : Type) [Field F] [Fintype F] (n : ℕ) (hn : 0 < n)
    (K : Finset (Fin n → F)) (hK : IsKakeyaFinite K) :
    (Fintype.card F : ℚ) ^ n / (2 - 1 / Fintype.card F) ^ (n - 1) ≤ K.card := by sorry

end FCP.Kakeya
