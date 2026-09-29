-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_exists_periodEquiv
-- name    : CerednikDrinfeld.Mumford.PeriodDatum.exists_periodEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/02c37328-f2d8-586b-aca2-1f6546537fe0
-- title:
--   Ribbon kernel realised as ker π via periods
-- statement:
--   Fix a finite type $E$ of edges and a type $V$ of vertices with decidable equality, and a degeneracy datum $D : \mathrm{DegeneracyData}\ E\ V$, that is, maps $a, b : E \to V$ together with widths $w : E \to \mathbb{N}^{+}$. The ribbon kernel `ribbonKernel D` is the submodule of $E \to \mathbb{Z}$ cut out as the intersection over $i \in \{0,1\}$ of the kernels of the two pushforward maps $(E \to \mathbb{Z}) \to (V \to \mathbb{Z})$ along $a$ and along $b$, and `ribbonGram D` is the width pairing $\langle x, y\rangle = \sum_{e} w(e)\, x(e)\, y(e)$ restricted to it. Let $K \subseteq L$ be fields with $L$ a $K$-algebra, and let $\mathrm{ord} : \mathrm{Additive}\ K^{\times} \to^{+} \mathbb{Z}$ be an additive map. Let $P$ be a period datum for $D$, $K$, $L$, $\mathrm{ord}$: a $\mathbb{Z}$-bilinear pairing $Q$ on `ribbonKernel D` with values in $\mathrm{Additive}\ K^{\times}$ which is symmetric and satisfies $\mathrm{ord}(Q(x,y)) = \mathrm{ribbonGram}\ D\ x\ y$ for all $x, y$. Write $P.\mathrm{TorusPoints} = \mathrm{Hom}_{\mathbb{Z}}(\mathrm{ribbonKernel}\ D, \mathrm{Additive}\ L^{\times})$, let `P.QL` be the associated $\mathbb{Z}$-linear map from `ribbonKernel D` to $P.\mathrm{TorusPoints}$ obtained from $Q$ by base change of units along $K \to L$, let `P.U` be the submodule `P.U` of $P.\mathrm{TorusPoints}$ and `P.π` the linear map defined on it. The assertion is that there is a $\mathbb{Z}$-linear isomorphism $e$ from `ribbonKernel D` onto $\ker(P.\pi)$ such that for every $x$ in the ribbon kernel the image of $e(x)$ in $P.\mathrm{TorusPoints}$, taken through the inclusions $\ker(P.\pi) \subseteq P.U \subseteq P.\mathrm{TorusPoints}$, is $P.\mathrm{QL}(x)$.
--
--   This is the statement that, for a Mumford-type period datum, the ribbon kernel is carried isomorphically by the period map $x \mapsto Q_L(x, \cdot)$ onto the kernel of the uniformisation map $\pi$, so that the lattice of periods is a faithful copy of the ribbon kernel. It is used in the construction of a toric uniformisation from a period uniformisation, [`CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization`](thm.html#CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_PeriodDatum_exists_periodEquiv.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.PeriodDatum.exists_periodEquiv
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) :
    ∃ e : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(LinearMap.ker P.π),
      ∀ x : ↥(ribbonKernel D), ((e x : ↥P.U) : P.TorusPoints) = P.QL x := by sorry
