-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_of_X_pow_mem_span_of_forall_isIdempotentElem
-- name    : CerednikDrinfeld.FormalODModule.exists_hasKernelOfDegree_of_X_pow_mem_span_of_forall_isIdempotentElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/8ba1356f-6a67-5205-a6dd-9e14ab0dddc5
-- title:
--   Constant kernel degree over a ring with connected spectrum
-- statement:
--   Let $B$ be a commutative Noetherian ring in which every idempotent element is $0$ or $1$, and let $\varphi$ be a `Series B`, that is a pair $(\varphi_0,\varphi_1)$ of power series in $B[\![X_0,X_1]\!]$ (formally, a map $\mathrm{Fin}\,2 \to \mathrm{MvPowerSeries}\,(\mathrm{Fin}\,2)\,B$), such that each $\varphi_i$ has zero constant coefficient and such that for some $N \in \mathbb{N}$ one has $X_i^N \in (\varphi_0,\varphi_1)$ for both $i$, the ideal being the span of the range of $\varphi$. The conclusion is that there exists $d \in \mathbb{N}$ with `FormalODModule.HasKernelOfDegree φ d`, i.e. the kernel algebra $\mathrm{KerAlgebra}\,\varphi = B[\![X_0,X_1]\!]/(\varphi_0,\varphi_1)$ is a finite $B$-module, is projective as a $B$-module, and for every field $\kappa$ and every ring homomorphism $f : B \to \kappa$ the $\kappa$-vector space $\kappa[\![X_0,X_1]\!]/(f_*\varphi_0, f_*\varphi_1)$, where $f_*$ denotes applying $f$ to coefficients, has dimension exactly $d$. Thus the degree is the same at all field-valued points of $B$.
--
--   This is the standard fact that a finite projective module over a ring with connected prime spectrum has constant rank, applied to the kernel algebra of a pair of power series cutting out a finite subscheme of a two-dimensional formal group; it supplies the degree appearing in `HasKernelOfDegree`. It is used in the rigidification of fake elliptic curves, via [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_hasKernelOfDegree_pow_two_mul_of_isODHom_of_represents`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_hasKernelOfDegree_pow_two_mul_of_isODHom_of_represents).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_of_X_pow_mem_span_of_forall_isIdempotentElem.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_hasKernelOfDegree_of_X_pow_mem_span_of_forall_isIdempotentElem
    {B : Type} [CommRing B] [IsNoetherianRing B]
    (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (φ : Series B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ)) :
    ∃ d : ℕ, FormalODModule.HasKernelOfDegree φ d := by sorry
