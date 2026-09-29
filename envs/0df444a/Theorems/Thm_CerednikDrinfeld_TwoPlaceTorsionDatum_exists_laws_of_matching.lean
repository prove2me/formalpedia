-- Prove2me | Theorems.Thm_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching
-- name    : CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_matching
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/7bec400c-e518-5817-b58a-639a721f5e8c
-- title:
--   Transport of two-place p-torsion data along matchings
-- statement:
--   Fix a natural number $p$ and eight finite index types $E_1,V_1,E_1',V_1',E_2,V_2,E_2',V_2'$ ($V$'s with decidable equality). For $i=1,2$ let $D_i$ on $(E_i,V_i)$ and $D_i'$ on $(E_i',V_i')$ be degeneracy data, each consisting of two maps $a,b\colon E\to V$ and a width $w\colon E\to\mathbb{Z}_{>0}$, equipped with Hecke data $H_i,H_i'$: commuting integral matrices $T(\ell)$ on $E$ and $T_v(\ell)$ on $V$ indexed by the primes, intertwining the pair of pushforward maps $\mathrm{jointDelta}$ away from a finite set of primes and preserving the joint kernel everywhere. Assume given matchings $M_i\colon H_i\to H_i'$, i.e. bijections $E_i\simeq E_i'$, $V_i\simeq V_i'$ compatible with $a$, $b$ and $w$, intertwining the Hecke matrices on all of $E_i\to\mathbb{Z}$ outside a finite set of primes and on $\mathrm{ribbonKernel}\,D_i$ at the remaining primes. Let $A_1,A_2$ be valuation subrings of $\overline{\mathbb{Q}}$ and let $\mathcal{J}$ be a two-place $p$-torsion datum for $(D_1,H_1)$, $(D_2,H_2)$ at $A_1,A_2$: a finite abelian group $T$ killed by $p$ with a ring homomorphism from $\mathbb{Z}[T_\ell:\ell]$ into $\mathrm{End}_{\mathbb{Z}}T$, a Galois action commuting with it and trivial on the subgroup fixing some finite extension of $\mathbb{Q}$, toric subgroups $\mathrm{toric}_i$ identified with $\mathrm{Hom}(\mathrm{ribbonKernel}\,D_i,\mathbb{Z}/p)$, and specialisation maps $\mathrm{sp}_i$ from the $A_i$-inertia invariants to $\mathrm{ribbonComponentGroup}\,D_i$. Given $M\in\mathbb{N}$, primes $r_1,r_2$ and the hypothesis that $\mathcal{J}$ satisfies $\mathrm{Laws}\,M\,r_1\,r_2$ (good reduction outside $M$ for its first constituent, together with the local laws at $r_1$ and at $r_2$ for its two constituents), the conclusion is the existence of a two-place $p$-torsion datum $\mathcal{J}'$ for $(D_1',H_1')$, $(D_2',H_2')$ at the same $A_1,A_2$ satisfying $\mathrm{Laws}\,M\,r_1\,r_2$.
--
--   This is the transport step for the Čerednik–Drinfeld style component-group data used in level lowering: a pair of matchings of Hecke degeneracy data carries a two-place $p$-torsion datum together with all its arithmetic laws to the matched data. It is cited in the construction of such a datum with its laws from a supersingular level datum, and its proof invokes the induced isometry of ribbon kernels intertwining the kernel Hecke operators, [`CerednikDrinfeld.ribbon_kernelEquiv`](thm.html#CerednikDrinfeld.ribbon_kernelEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.lean

import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld

theorem CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_matching
    {p : ℕ} {E₁ V₁ E₁' V₁' E₂ V₂ E₂' V₂' : Type}
    [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₁'] [Fintype V₁'] [DecidableEq V₁']
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂] [Fintype E₂'] [Fintype V₂'] [DecidableEq V₂']
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₁' : DegeneracyData E₁' V₁'} {H₁' : HeckeData D₁'}
    {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂} {D₂' : DegeneracyData E₂' V₂'} {H₂' : HeckeData D₂'}
    (M₁ : Matching H₁ H₁') (M₂ : Matching H₂ H₂')
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}
    (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    (M : ℕ) (r₁ r₂ : ℕ) [Fact r₁.Prime] [Fact r₂.Prime]
    (h𝒥 : 𝒥.Laws M r₁ r₂) :
    ∃ 𝒥' : TwoPlaceTorsionDatum p D₁' H₁' D₂' H₂' A₁ A₂, 𝒥'.Laws M r₁ r₂ := by sorry
