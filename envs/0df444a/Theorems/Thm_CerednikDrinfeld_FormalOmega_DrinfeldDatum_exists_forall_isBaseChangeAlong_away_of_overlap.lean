-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_forall_isBaseChangeAlong_away_of_overlap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/27e896d7-5f1c-56a5-9cd4-04c9805b5958
-- title:
--   Zariski gluing of Drinfeld data along a basic open cover
-- statement:
--   Fix a commutative ring $\mathcal O$, a field $K$ that is an $\mathcal O$-algebra, an element $\pi \in \mathcal O$, and a commutative $\mathcal O$-algebra $B$. Let $f : \mathrm{Fin}\,k \to B$ be a finite family generating the unit ideal of $B$. Suppose given, for each $i$, a Drinfeld datum $Q_i$ over $B[1/f_i] =$ `Localization.Away (f i)` — that is, two assignments $N_0, N_1$ from $\operatorname{Spec}$ of the base to $\mathcal O$-submodules of $K^2$, each finitely generated and spanning $K^2$ over $K$, with $N_0(x) \le N_1(x)$ and $\pi N_1(x) \subseteq N_0(x)$, the sets $\{x : v \in N_\epsilon(x)\}$ open for every $v \in K^2$, together with invertible modules $T_0, T_1$ over the base, maps $\Pi_0 : T_0 \to T_1$ and $\Pi_1 : T_1 \to T_0$ whose two composites are multiplication by $\pi$, and identifications $u_0, u_1$ of the base changes of the lattices $N_0(x), N_1(x)$ to the local ring at $x$ with the stalks of $T_0, T_1$ at $x$, compatible with the inclusion $N_0(x) \subseteq N_1(x)$, with $\Pi_0$, and with multiplication by $\pi$. Suppose given, for each pair $(i,j)$, a commutative ring $C_{ij}$ which is a localisation of $B$ away from $f_i f_j$ and an algebra over $\mathcal O$, over $B$, and over each of $B[1/f_i]$ and $B[1/f_j]$, all compatibly, and a single Drinfeld datum $Q_{ij}$ over $C_{ij}$ which is a base change of $Q_i$ along $B[1/f_i] \to C_{ij}$ and also a base change of $Q_j$ along $B[1/f_j] \to C_{ij}$; here a base change along an $\mathcal O$-algebra map $g$ means the existence of equalities $N_\epsilon'(x') = N_\epsilon(g^{-1}x')$ of lattices at corresponding points together with $g$-semilinear maps $\tau_0, \tau_1$ on the invertible modules whose images span after extension of scalars and which are compatible with $\Pi_0$, $\Pi_1$ and with the stalk identifications $u_0, u_1$. The conclusion is that there is a Drinfeld datum $Q$ over $B$ such that for every $i$ the datum $Q_i$ is a base change of $Q$ along $B \to B[1/f_i]$. No cocycle condition on triple overlaps is assumed.
--
--   This is the Zariski descent (sheaf) property of Drinfeld's functor of quadruples: data given on the members of a finite basic open cover, with a common base change on each pairwise overlap, come from a datum on the base; the absence of a triple-overlap condition reflects the rigidity of such data. It is used in the construction of a Drinfeld datum attached to a Deligne datum from local data on a basic open cover, via [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_forall_away`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_forall_away).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_forall_isBaseChangeAlong_away_of_overlap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (C : Fin k → Fin k → Type) [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)] [∀ i j, Algebra 𝒪 (C i j)]
    [∀ i j, IsScalarTower 𝒪 B (C i j)] [∀ i j, IsLocalization.Away (f i * f j) (C i j)]
    [∀ i j, Algebra (Localization.Away (f i)) (C i j)] [∀ i j, Algebra (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower 𝒪 (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j)]
    (Q₂ : ∀ i j : Fin k, DrinfeldDatum (K := K) π (C i j))
    (hl : ∀ i j : Fin k, (Q i).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j))
    (hr : ∀ i j : Fin k, (Q j).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j)) :
    ∃ Qg : DrinfeldDatum (K := K) π B,
      ∀ i : Fin k, Qg.IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) (Q i) := by sorry
