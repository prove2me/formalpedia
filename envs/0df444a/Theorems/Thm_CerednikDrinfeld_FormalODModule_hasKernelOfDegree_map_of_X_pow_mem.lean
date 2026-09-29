-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map_of_X_pow_mem
-- name    : CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map_of_X_pow_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/f2d5018a-2547-566c-9dc4-1f6ea73f579b
-- title:
--   Base change preserves kernel algebras of degree d
-- statement:
--   Let $B$ and $B'$ be commutative rings (in the same universe), $g \colon B \to B'$ a ring homomorphism, and let $\varphi = (\varphi_0,\varphi_1)$ be a pair of two-variable formal power series over $B$, i.e. an element of `Series B` $= \mathrm{Fin}\,2 \to B[[X_0,X_1]]$, each $\varphi_i$ having zero constant coefficient. Assume $\varphi$ has a kernel algebra of degree $d$ in the sense of `FormalODModule.HasKernelOfDegree`: the quotient $B[[X_0,X_1]]/(\varphi_0,\varphi_1)$, where the ideal is the span of the range of $\varphi$, is finite as a $B$-module, projective as a $B$-module, and for every field $\kappa$ and every ring homomorphism $f \colon B \to \kappa$ the $\kappa$-vector space $\kappa[[X_0,X_1]]/(f_*\varphi_0, f_*\varphi_1)$ has dimension $d$, where $f_*$ denotes coefficientwise application of $f$. Assume further that there is a natural number $N$ with $X_i^N \in (\varphi_0,\varphi_1)$ for both $i \in \mathrm{Fin}\,2$. The conclusion is that the base-changed pair $\varphi.map\ g = (g_*\varphi_0, g_*\varphi_1)$ over $B'$ again satisfies `HasKernelOfDegree` with the same $d$: its kernel algebra $B'[[X_0,X_1]]/(g_*\varphi_0,g_*\varphi_1)$ is finite and projective over $B'$, and has dimension $d$ over every field receiving a homomorphism from $B'$.
--
--   This is the base-change stability of the finite locally free kernel of a pair of power series, the algebraic substance behind the statement that kernels of isogenies of formal modules of fixed degree are preserved under base change; the nilpotence hypothesis $X_i^N \in (\varphi)$ makes the kernel algebra a quotient of a truncated polynomial algebra, so that formation of the quotient commutes with $- \otimes_B B'$. It is used in [`CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map`](thm.html#CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map) and in [`CerednikDrinfeld.FormalODModule.act_pow_mem_span_of_isODHom_of_hasKernelOfDegree`](thm.html#CerednikDrinfeld.FormalODModule.act_pow_mem_span_of_isODHom_of_hasKernelOfDegree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map_of_X_pow_mem.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map_of_X_pow_mem
    {B B' : Type u} [CommRing B] [CommRing B'] (g : B →+* B') (φ : Series B)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d)
    (N : ℕ) (hN : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ)) :
    FormalODModule.HasKernelOfDegree (φ.map g) d := by sorry
