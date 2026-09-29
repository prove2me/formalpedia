-- Prove2me | Theorems.Thm_DeligneSerre_charZero_quotient
-- name    : DeligneSerre.charZero_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/ee79acdb-a39c-5921-b796-95db48ddab3e
-- title:
--   Characteristic zero for a quotient by an ideal meeting ℤ trivially
-- statement:
--   Let $T$ be a commutative ring and let $\mathfrak{p}$ be an ideal of $T$. Assume that the structure map $\mathbb{Z} \to T$ (the canonical algebra map, which sends $n$ to $n \cdot 1_T$) pulls $\mathfrak{p}$ back to the zero ideal in the strong sense that for every integer $n$, if the image of $n$ in $T$ lies in $\mathfrak{p}$, then $n = 0$. The conclusion is that the quotient ring $T/\mathfrak{p}$ is of characteristic zero, i.e. it carries a `CharZero` instance: the canonical map $\mathbb{N} \to T/\mathfrak{p}$ sending $m$ to $m \cdot 1$ is injective. Note that the hypothesis is about integers mapping into $\mathfrak{p}$, with no primality, properness or finiteness assumption on $\mathfrak{p}$ and no hypothesis on $T$ beyond commutativity; in particular $\mathfrak{p} = T$ is excluded automatically, since then the image of $1$ would lie in $\mathfrak{p}$.
--
--   A routine criterion for a quotient ring to have characteristic zero, used to pass from a ring with possible torsion phenomena to a characteristic-zero residue ring. It is invoked in the Deligne–Serre lifting argument, where $T$ is a Hecke algebra and $\mathfrak{p}$ a prime ideal attached to an eigensystem: it feeds [`CuspForm.exists_isNormalizedEigenform_ker_le_of_isPrime`](thm.html#CuspForm.exists_isNormalizedEigenform_ker_le_of_isPrime), [`DeligneSerre.exists_charZero_eigenvector_of_residual_character`](thm.html#DeligneSerre.exists_charZero_eigenvector_of_residual_character) and [`DeligneSerre.exists_factorization_charZero_quotient`](thm.html#DeligneSerre.exists_factorization_charZero_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_charZero_quotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem DeligneSerre.charZero_quotient {T : Type*} [CommRing T] (𝔭 : Ideal T)
  (h𝔭 : ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) : CharZero (T ⧸ 𝔭) := by sorry
