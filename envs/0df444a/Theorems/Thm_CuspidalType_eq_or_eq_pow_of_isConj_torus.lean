-- Prove2me | Theorems.Thm_CuspidalType_eq_or_eq_pow_of_isConj_torus
-- name    : CuspidalType.eq_or_eq_pow_of_isConj_torus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/a494fac3-45f2-5832-b348-bc91438419ce
-- title:
--   Conjugate non-split torus elements differ by Frobenius
-- statement:
--   Let $q$ be a natural number carrying the hypothesis that it is prime, and let $\alpha,\alpha'$ be units of the field `GaloisField q 2` with $q^2$ elements. Here `torus q` denotes the monoid homomorphism $(\mathbb{F}_{q^2})^\times \to$ `GL2 q` obtained by applying `Units.map` to the algebra homomorphism that sends an element of $\mathbb{F}_{q^2}$ to the matrix, in the fixed basis `quadBasis q` of $\mathbb{F}_{q^2}$ as a two-dimensional $\mathbb{Z}/q$-vector space, of the $\mathbb{Z}/q$-linear map given by multiplication by that element; the basis `quadBasis q` is the one produced from the fact that $\mathbb{F}_{q^2}$ has $\mathbb{Z}/q$-rank $2$. The hypothesis is that the two matrices `torus q α` and `torus q α'` are conjugate in `GL2 q`, in the sense of Mathlib's `IsConj`. The conclusion is the disjunction $\alpha' = \alpha$ or $\alpha' = \alpha^{q}$. No regularity or non-rationality assumption on $\alpha$ is imposed: when $\alpha$ lies in the prime field the two alternatives coincide.
--
--   This is the injectivity-up-to-Frobenius statement for the embedding of the non-split torus $\mathbb{F}_{q^2}^\times$ into $\mathrm{GL}_2(\mathbb{F}_q)$: a torus element is determined by its $\mathrm{GL}_2(\mathbb{F}_q)$-conjugacy class up to the action of $\mathrm{Gal}(\mathbb{F}_{q^2}/\mathbb{F}_q)$. It is used in the counting of elliptic conjugacy classes entering [`CuspidalType.NV3Arch.sum_elliptic_eq`](thm.html#CuspidalType.NV3Arch.sum_elliptic_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_eq_or_eq_pow_of_isConj_torus.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.eq_or_eq_pow_of_isConj_torus (q : ℕ) [Fact q.Prime] {α α' : (GaloisField q 2)ˣ}
    (h : IsConj (torus q α) (torus q α')) : α' = α ∨ α' = α ^ q := by sorry
