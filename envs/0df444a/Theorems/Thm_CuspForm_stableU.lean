-- Prove2me | Theorems.Thm_CuspForm_stableU
-- name    : CuspForm.stableU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/13cb3df8-f393-5731-b9e4-fc64100c9609
-- title:
--   U_q preserves cusp forms on Γ_H(M)
-- statement:
--   Let $M$ be a nonzero natural number, $H$ a subgroup of $(\mathbb{Z}/M)^\times$, $k$ an integer, and $q$ a prime dividing $M$. The assertion is the predicate [`CuspForm.StableU M H k q`](def/CuspForm_HeckeOperatorFormsGammaH.html#L77), which says: for every cusp form $f$ of weight $k$ for the group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) — the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained by pulling $H$ back along `gamma0Units M` to a subgroup of $\Gamma_0(M)$ and pushing forward along the inclusion of $\Gamma_0(M)$, regarded via the canonical map as a subgroup of $\mathrm{GL}(2,\mathbb{R})$ — the function $$\mathrm{heckeU}\,k\,q\,f=\sum_{j=0}^{q-1} f\mid_k \mathrm{heckeMatrix}\,q\,j$$ has the three properties: (i) $(\mathrm{heckeU}\,k\,q\,f)\mid_k\gamma=\mathrm{heckeU}\,k\,q\,f$ for every $\gamma$ in that subgroup of $\mathrm{GL}(2,\mathbb{R})$; (ii) it is differentiable as a map between the complex manifolds given by the self-models of $\mathbb{C}$, i.e. holomorphic on the upper half-plane; and (iii) for every point $c$ of $\mathbb{P}^1(\mathbb{R})$ which is a cusp of that subgroup, it is zero at $c$ in weight $k$ in the sense of `OnePoint.IsZeroAt`.
--
--   This is the statement that the operator $U_q$ at a prime $q$ dividing the level preserves the space of weight-$k$ cusp forms for $\Gamma_H(M)$; it discharges the hypothesis under which the $U_q$-operator on cusp forms for $\Gamma_H(M)$ is constructed as a linear endomorphism. It is used throughout the Eichler–Shimura and Hecke-eigenform constructions at level $\Gamma_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_stableU.lean

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.stableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) :
    CuspForm.StableU M H k q := by sorry
