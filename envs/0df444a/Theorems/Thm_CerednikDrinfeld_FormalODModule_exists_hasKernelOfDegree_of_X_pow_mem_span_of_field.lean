-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_of_X_pow_mem_span_of_field
-- name    : CerednikDrinfeld.FormalODModule.exists_hasKernelOfDegree_of_X_pow_mem_span_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/72ffa765-cc13-59dc-acd3-cdff69900556
-- title:
--   Existence of a kernel degree over a field
-- statement:
--   Let $k$ be a field and let $\varphi = (\varphi_0,\varphi_1)$ be an element of `Series k`, i.e. a pair of power series in $k[[X_0,X_1]]$ (a map $\mathrm{Fin}\,2 \to$ `MvPowerSeries (Fin 2) k`), subject to two hypotheses: each $\varphi_i$ has vanishing constant coefficient, and there is a natural number $N$ with $X_i^N \in (\varphi_0,\varphi_1)$ for both $i$, the ideal being the span of the range of $\varphi$. The conclusion asserts the existence of a natural number $d$ for which `FormalODModule.HasKernelOfDegree φ d` holds, that is, writing $A(\varphi) = k[[X_0,X_1]]/(\varphi_0,\varphi_1)$ for the kernel algebra: $A(\varphi)$ is a finite $k$-module, it is a projective $k$-module, and for every field $\kappa$ and every ring homomorphism $f : k \to \kappa$ the $\kappa$-dimension of $\kappa[[X_0,X_1]]/(f\varphi_0, f\varphi_1)$, the kernel algebra of the coefficientwise image $\varphi$ under $f$, equals $d$. No formal group or $\mathcal{O}_D$-action is involved in the statement; only the pair of power series enters.
--
--   This supplies the degree of the kernel of an isogeny of formal $\mathcal{O}_D$-modules over a field, in the form used throughout the Čerednik–Drinfel'd part of the development: the finite flatness statement for $k[[X_0,X_1]]/(\varphi)$ once the cokernel is known to be infinitesimal, expressed by the nilpotence condition $X_i^N \in (\varphi)$. It is invoked by the results on degrees of composites and powers of isogenies, in particular by the computations of kernel degrees for endomorphisms of special formal $\mathcal{O}_D$-modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_of_X_pow_mem_span_of_field.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_hasKernelOfDegree_of_X_pow_mem_span_of_field
    {k : Type} [Field k] (φ : Series k)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) ^ N ∈ Ideal.span (Set.range φ)) :
    ∃ d : ℕ, FormalODModule.HasKernelOfDegree φ d := by sorry
