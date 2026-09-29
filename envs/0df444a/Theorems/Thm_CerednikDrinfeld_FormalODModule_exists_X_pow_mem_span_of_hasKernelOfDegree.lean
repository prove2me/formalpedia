-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
-- name    : CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/ccf78e00-15a5-50a6-8a5c-929be9465090
-- title:
--   Nilpotence of the variables modulo a kernel ideal of constant degree
-- statement:
--   Let $B$ be a commutative Noetherian ring and let $\varphi : \mathrm{Fin}\,2 \to B[[X_0,X_1]]$ be a pair of formal power series in two variables over $B$ (the type `Series B`), each with vanishing constant coefficient. Assume `FormalODModule.HasKernelOfDegree` $\varphi\ d$ for some natural number $d$, that is: the quotient algebra $\mathrm{KerAlgebra}\,\varphi = B[[X_0,X_1]]/(\varphi_0,\varphi_1)$, where the ideal is the span of the range of $\varphi$, is a finite $B$-module and a projective $B$-module, and for every field $\kappa$ and every ring homomorphism $f : B \to \kappa$ the $\kappa$-vector space $\kappa[[X_0,X_1]]/(f(\varphi_0), f(\varphi_1))$, obtained by applying $f$ to the coefficients of $\varphi$, has finite dimension exactly $d$. The conclusion is that there exists a natural number $N$ such that for both $i \in \mathrm{Fin}\,2$ one has $X_i^{N} \in (\varphi_0,\varphi_1)$ in $B[[X_0,X_1]]$, a single $N$ serving for both variables.
--
--   This is the statement that the augmentation ideal of the kernel algebra of $\varphi$ is nilpotent, i.e. that the finite locally free group scheme cut out by $\varphi$ is infinitesimal; the force of the hypothesis is that the rank $d$ is the same at all field-valued points of $B$, generic ones included. It underlies the basic manipulations of the degree of a kernel in the formal $\mathcal{O}_D$-module theory, being used for instance by [`CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp`](thm.html#CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp) and [`CerednikDrinfeld.FormalODModule.HasKernelOfDegree.dvd_of_comp`](thm.html#CerednikDrinfeld.FormalODModule.HasKernelOfDegree.dvd_of_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree
    {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) :
    ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ) := by sorry
