-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
-- name    : CerednikDrinfeld.FormalOmega.exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/7f36465b-28a5-5a82-a07e-288c493b37d8
-- title:
--   Gluing submodule-valued functions along a basic open cover of Spec B
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field which is an $\mathcal O$-algebra, and $B$ a commutative $\mathcal O$-algebra. Let $k \in \mathbb N$ and let $f : \mathrm{Fin}\,k \to B$ be a family of elements whose span as an ideal is all of $B$. Suppose given, for each index $i$, a function $N_i$ assigning to every prime of the localization $B[1/f_i]$ an $\mathcal O$-submodule $N_i(y)$ of $K^2 = (\mathrm{Fin}\,2 \to K)$, subject to two hypotheses: (i) for every $i$ and every $v \in K^2$ the membership locus $\{y : v \in N_i(y)\}$ is open in $\operatorname{Spec} B[1/f_i]$; (ii) for all indices $i, j$ and primes $y$ of $B[1/f_i]$, $z$ of $B[1/f_j]$, if the images of $y$ and $z$ under the maps on prime spectra induced by the structure algebra maps $B \to B[1/f_i]$, $B \to B[1/f_j]$ (written with `DrinfeldDatum.pointUnder`, i.e. `PrimeSpectrum.comap`) coincide, then $N_i(y) = N_j(z)$. The conclusion asserts the existence of a function $N_g$ from $\operatorname{Spec} B$ to $\mathcal O$-submodules of $K^2$ such that $N_g$ of the image of $y$ in $\operatorname{Spec} B$ equals $N_i(y)$ for every $i$ and every prime $y$ of $B[1/f_i]$, and such that for every $v \in K^2$ the locus $\{x \in \operatorname{Spec} B : v \in N_g(x)\}$ is open.
--
--   This is the Zariski gluing step for the lattice data of a Drinfeld datum: a family of submodules of $K^2$ indexed by the points of a basic open cover, with open membership loci and agreeing over common points of the base, descends to a single such family on $\operatorname{Spec} B$. It is used in the construction of the lattice functions $N_0$, $N_1$ of a Drinfeld datum by gluing over a finite cover by basic opens, and is cited by [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_forall_isBaseChangeAlong_away_of_overlap`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_forall_isBaseChangeAlong_away_of_overlap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (N : ∀ i : Fin k, PrimeSpectrum (Localization.Away (f i)) → Submodule 𝒪 (Fin 2 → K))
    (hN : ∀ (i : Fin k) (v : Fin 2 → K), IsOpen {y : PrimeSpectrum (Localization.Away (f i)) | v ∈ N i y})
    (hcompat : ∀ (i j : Fin k) (y : PrimeSpectrum (Localization.Away (f i))) (z : PrimeSpectrum (Localization.Away (f j))),
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y =
        DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z → N i y = N j z) :
    ∃ Ng : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K),
      (∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
          Ng (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = N i y) ∧
      ∀ v : Fin 2 → K, IsOpen {x : PrimeSpectrum B | v ∈ Ng x} := by sorry
