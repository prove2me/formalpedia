-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_U_divisible
-- name    : CerednikDrinfeld.Mumford.PeriodDatum.U_divisible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/e5905424-5c40-5ca2-bf43-493345b8f86f
-- title:
--   The group U of a period datum is divisible
-- statement:
--   Let $E$ be a finite type and $V$ a type with decidable equality, and let $D$ be a degeneracy datum on $(E,V)$, that is, two maps $a,b\colon E\to V$ together with widths $w\colon E\to\mathbb{N}_{>0}$. Let $K\subseteq L$ be fields with $L$ a $K$-algebra, and let $\mathrm{ord}\colon \mathrm{Additive}\,K^\times\to\mathbb{Z}$ be an additive homomorphism. Let $P$ be a period datum for $D$ over $(K,L,\mathrm{ord})$: a $\mathbb{Z}$-bilinear form $Q$ on the ribbon kernel $\operatorname{ribbonKernel} D$ (the intersection over $i$ of the kernels of the maps $\operatorname{jointDelta} D\,i$ inside $E\to\mathbb{Z}$) with values in $\mathrm{Additive}\,K^\times$, subject to $Q(x,y)=Q(y,x)$ and $\mathrm{ord}(Q(x,y))=\operatorname{ribbonGram} D\,x\,y$, the latter being the width pairing for $e\mapsto w(e)$ restricted to the ribbon kernel in both arguments. Assume that $L^\times$ is divisible: for every $x\in L^\times$ and every $n>0$ there is $y\in L^\times$ with $y^n=x$. The conclusion is that the submodule $P.U$ of $P$'s torus points — the preimage, under the quotient map onto $P.\mathrm{TorusPoints}$ modulo the period lattice $P.\mathrm{periodLattice}$, of the torsion submodule of that quotient — is divisible: for every $u\in P.U$ and every $n>0$ there is $u'\in P.U$ with $n\cdot u'=u$.
--
--   This is the divisibility clause required of the uniformising group in Mumford's analytic construction of a degenerating curve from a period datum, in the form used for the Čerednik–Drinfeld model; the hypothesis on $L^\times$ holds for instance when $L$ is algebraically closed or is the completion of an algebraic closure of a local field. It is cited in the construction of a toric uniformisation from a period uniformisation, [`CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization`](thm.html#CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_PeriodDatum_U_divisible.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.PeriodDatum.U_divisible
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) (hroots : ∀ (x : Lˣ) (n : ℕ), 0 < n → ∃ y : Lˣ, y ^ n = x) :
    ∀ u : ↥P.U, ∀ n : ℕ, 0 < n → ∃ u' : ↥P.U, n • u' = u := by sorry
