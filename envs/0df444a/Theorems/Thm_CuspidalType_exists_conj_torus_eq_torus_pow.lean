-- Prove2me | Theorems.Thm_CuspidalType_exists_conj_torus_eq_torus_pow
-- name    : CuspidalType.exists_conj_torus_eq_torus_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/04dec8e5-639a-51ef-9414-9ce2dc049d6b
-- title:
--   Frobenius conjugates the non-split torus of GL₂(𝔽_q)
-- statement:
--   Let $q$ be a prime number, let $\mathbb{F}_q =$ `ZMod q`, and write `GL2 q` for the group $\mathrm{GL}_2(\mathbb{F}_q)$ of invertible $2\times 2$ matrices over $\mathbb{F}_q$ (Mathlib's `Matrix.GeneralLinearGroup (Fin 2) (ZMod q)`). Let `GaloisField q 2` be the field with $q^2$ elements, regarded as an $\mathbb{F}_q$-algebra, and let `quadBasis q` be the $\mathbb{F}_q$-basis of it indexed by `Fin 2` obtained from the fact that its $\mathbb{F}_q$-dimension is $2$. The monoid homomorphism `torus q` from $\mathbb{F}_{q^2}^\times$ to $\mathrm{GL}_2(\mathbb{F}_q)$ is the one induced on unit groups by the $\mathbb{F}_q$-algebra map sending $\alpha \in \mathbb{F}_{q^2}$ to the matrix, in the basis `quadBasis q`, of the $\mathbb{F}_q$-linear map $x \mapsto \alpha x$; thus `torus q` is the non-split torus of $\mathrm{GL}_2(\mathbb{F}_q)$ written in that fixed basis. The assertion is that there exists a single matrix $f \in \mathrm{GL}_2(\mathbb{F}_q)$ with $f \cdot \mathrm{torus}(\alpha) \cdot f^{-1} = \mathrm{torus}(\alpha^q)$ for every $\alpha \in \mathbb{F}_{q^2}^\times$, the element $f$ being independent of $\alpha$.
--
--   This records that $\mathrm{torus}(\alpha)$ and $\mathrm{torus}(\alpha^q)$ are conjugate in $\mathrm{GL}_2(\mathbb{F}_q)$, i.e. that the elliptic conjugacy classes of $\mathrm{GL}_2(\mathbb{F}_q)$ are indexed by Frobenius-orbits $\{\alpha,\alpha^q\}$ in $\mathbb{F}_{q^2}^\times$. It is used in the work on characters of cuspidal type, in [`CuspidalType.NV3Arch.sum_elliptic_eq`](thm.html#CuspidalType.NV3Arch.sum_elliptic_eq) and in [`CuspidalType.finsupp_apply_pow_eq_of_forall_character_torus_eq_sum`](thm.html#CuspidalType.finsupp_apply_pow_eq_of_forall_character_torus_eq_sum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_exists_conj_torus_eq_torus_pow.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_conj_torus_eq_torus_pow (q : ℕ) [Fact q.Prime] :
    ∃ f : GL2 q, ∀ α : (GaloisField q 2)ˣ, f * torus q α * f⁻¹ = torus q (α ^ q) := by sorry
