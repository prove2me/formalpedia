-- Prove2me | Theorems.Thm_CohCarrier_jDegL_mem_parabolicHoms
-- name    : CohCarrier.jDegL_mem_parabolicHoms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/2bbf9a3e-1531-51ca-8c94-1a956a4f66cf
-- title:
--   Corestriction along degeneracy maps preserves parabolic homomorphisms
-- statement:
--   Let $M$, $M'$ and $d$ be natural numbers with $M'$ and $d$ nonzero, let $A$ be an additive abelian group which is a module over a semiring $R$, and let $h$ be a level datum [`CohCarrier.LevelLE M M' ⊤ ⊤ d`](def/CohCarrier_Level.html#L330), that is: $M \mid M'$, $d \mid M'/M$, and the condition on reduction of unit groups, which is vacuous here because both character subgroups are taken to be $\top$. For a level $N$ and the full subgroup $\top \le (\mathbb{Z}/N)^\times$, [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133) is the image in $\mathrm{SL}_2(\mathbb{Z})$ of $\Gamma_0(N)$, and [`CohCarrier.H1 N ⊤ A`](def/CohCarrier_Level.html#L162) is the group of additive homomorphisms $\mathrm{Additive}\,\Gamma_0(N) \to A$. Let $y \in$ [`CohCarrier.H1 M' ⊤ A`](def/CohCarrier_Level.html#L162) lie in the submodule [`ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M' ⊤) A`](def/ModularCurve_PeriodMap.html#L62), i.e. $y(\gamma) = 0$ for every $\gamma \in \Gamma_0(M')$ whose matrix has trace with square $4$ (trace $\pm 2$). The conclusion is that the image of $y$ under the $R$-linear map [`CohCarrier.jDegL M M' ⊤ ⊤ d A R h`](def/CohCarrier_Level.html#L492) lies in [`ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M ⊤) A`](def/ModularCurve_PeriodMap.html#L62); here `jDegL` sends $y$ to the additive transfer (`coresAdd`) from the range of the degeneracy homomorphism `iotaDeg M M' ⊤ ⊤ d h` up to $\Gamma_0(M)$ of the character on that range obtained by transporting $y$ along the isomorphism of $\Gamma_0(M')$ with that range. Thus the corestricted character again vanishes on all elements of $\Gamma_0(M)$ of trace $\pm 2$.
--
--   This is the statement that the degeneracy corestriction maps on first cohomology with arbitrary coefficients respect the parabolic (cuspidal) part, the analogue for degeneracy maps of the corresponding stability statement for Hecke operators. It is used in the construction of a perfect self-adjoint pairing on the parabolic part compatible with the degeneracy adjoints, [`CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms`](thm.html#CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDegL_mem_parabolicHoms.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.jDegL_mem_parabolicHoms (M M' d : ℕ) [NeZero M'] [NeZero d]
    (A : Type*) [AddCommGroup A] (R : Type*) [Semiring R] [Module R A]
    (h : CohCarrier.LevelLE M M' ⊤ ⊤ d) (y : CohCarrier.H1 M' ⊤ A)
    (hy : y ∈ ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M' ⊤) A) :
    CohCarrier.jDegL M M' ⊤ ⊤ d A R h y ∈ ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M ⊤) A := by sorry
