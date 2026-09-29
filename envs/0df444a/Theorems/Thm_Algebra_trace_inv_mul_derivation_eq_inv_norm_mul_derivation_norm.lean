-- Prove2me | Theorems.Thm_Algebra_trace_inv_mul_derivation_eq_inv_norm_mul_derivation_norm
-- name    : Algebra.trace_inv_mul_derivation_eq_inv_norm_mul_derivation_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/fd6ea124-35ab-5676-9c2b-43c446ed9457
-- title:
--   Trace of logarithmic derivative equals logarithmic derivative of norm
-- statement:
--   Let $R$ be a commutative ring, let $F$ and $F'$ be fields carrying $R$-algebra structures, and let $F'$ be an $F$-algebra (no compatibility between the $R$-algebra structures and the $F$-algebra structure on $F'$ is assumed, and no finiteness or separability hypothesis is imposed). Let $d$ be an $R$-derivation of $F$ with values in $F$ and $d'$ an $R$-derivation of $F'$ with values in $F'$, and suppose $d'$ extends $d$ along the structure map $F \to F'$, i.e. $d'(\iota x) = \iota(d x)$ for all $x \in F$, where $\iota$ denotes `algebraMap F F'`. Then for every $h \in F'$,
--   $$\operatorname{Tr}_{F'/F}\bigl(h^{-1} \, d' h\bigr) = N_{F'/F}(h)^{-1} \, d\bigl(N_{F'/F}(h)\bigr),$$
--   with $\operatorname{Tr}_{F'/F}$ and $N_{F'/F}$ Mathlib's `Algebra.trace` and `Algebra.norm`. Since inversion is total with $0^{-1} = 0$, the case $h = 0$ is included and both sides are then $0$; likewise, when $F'$ is not a finite free $F$-module the trace is $0$ and the norm is $1$, so both sides vanish and the assertion holds vacuously.
--
--   This is the identity $\operatorname{Tr}_{F'/F} \circ \mathrm{dlog} = \mathrm{dlog} \circ N_{F'/F}$ for a derivation of the base field extended to the top field; it is the algebraic source of the compatibility of traces of differentials with norms of functions. It is used in the form [`AlgebraicCurve.traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm`](thm.html#AlgebraicCurve.traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm) for function fields of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_trace_inv_mul_derivation_eq_inv_norm_mul_derivation_norm.lean

import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Derivation.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.trace_inv_mul_derivation_eq_inv_norm_mul_derivation_norm {R F F' : Type*} [CommRing R] [Field F] [Field F'] [Algebra R F] [Algebra R F'] [Algebra F F'] (d : Derivation R F F) (d' : Derivation R F' F') (hd : ∀ x : F, d' (algebraMap F F' x) = algebraMap F F' (d x)) (h : F') : Algebra.trace F F' (h⁻¹ * d' h) = (Algebra.norm F h)⁻¹ * d (Algebra.norm F h) := by sorry
