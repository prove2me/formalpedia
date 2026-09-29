-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_pi_surj_torsion
-- name    : CerednikDrinfeld.Mumford.PeriodDatum.pi_surj_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/2dac9d9b-346a-5041-8902-d135f5113660
-- title:
--   Torsion points of a period Jacobian lie in imπ
-- statement:
--   Fix a finite type $E$ and a type $V$ with decidable equality, and a degeneracy datum $D : \mathrm{DegeneracyData}\ E\ V$, that is, maps $a, b \colon E \to V$ together with widths $w \colon E \to \mathbb{N}^{+}$. Fix fields $K$ and $L$ with $L$ a $K$-algebra, an additive homomorphism $\mathrm{ord} \colon \mathrm{Additive}\ K^{\times} \to \mathbb{Z}$, and a period datum $P$ for $D$, $K$, $L$, $\mathrm{ord}$: a $\mathbb{Z}$-bilinear form $Q$ on the ribbon kernel $\mathrm{ribbonKernel}\ D = \bigcap_i \ker(\mathrm{jointDelta}\ D\ i) \subseteq (E \to \mathbb{Z})$ with values in $\mathrm{Additive}\ K^{\times}$, which is symmetric and satisfies $\mathrm{ord}(Q(x,y)) = (\mathrm{ribbonGram}\ D)(x)(y)$, the width pairing of $w$ restricted to the ribbon kernel. Write $\mathrm{TorusPoints} = \mathrm{Hom}_{\mathbb{Z}}(\mathrm{ribbonKernel}\ D, \mathrm{Additive}\ L^{\times})$, let $\mathrm{periodLattice}$ be the range of the $L$-valued form $P.\mathrm{QL}$ inside it, and let $\mathrm{JacPoints}$ be the quotient module $\mathrm{TorusPoints}/\mathrm{periodLattice}$. Let $n$ be a natural number with $n > 0$. The assertion is that every $t \in \mathrm{JacPoints}$ killed by $n$, i.e. with $n \bullet t = 0$, is of the form $P.\pi\,u$ for some $u$ in the submodule $P.U$ of $\mathrm{TorusPoints}$, where $P.U$ is the preimage under the quotient map of the torsion submodule of $\mathrm{JacPoints}$ and $P.\pi$ is the quotient map restricted to it.
--
--   This is the $n$-torsion case of the statement that the image of $\pi$ contains all torsion of the abstract Jacobian attached to a period datum, in exactly the shape demanded by the surjectivity clause of a toric uniformisation. It is used by [`CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization`](thm.html#CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization) to produce a toric uniformisation from a period uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_PeriodDatum_pi_surj_torsion.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.PeriodDatum.pi_surj_torsion
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) {n : ℕ} (hn : 0 < n) :
    ∀ t : P.JacPoints, n • t = 0 → ∃ u : ↥P.U, P.π u = t := by sorry
