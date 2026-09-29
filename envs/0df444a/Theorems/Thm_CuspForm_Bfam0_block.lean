-- Prove2me | Theorems.Thm_CuspForm_Bfam0_block
-- name    : CuspForm.Bfam0.block
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/a0dd842e-cdbf-50b2-bca1-ff4b0e1a0a9f
-- title:
--   Chosen pairing family on parabolic cohomology: perfect and adjoint
-- statement:
--   Let $\mathcal O$ be a commutative ring which is a local integral domain of characteristic zero, and let $p$ be a prime with $p \neq 2$ such that $p$ is not a unit in $\mathcal O$. Write $\Gamma_0(M)$ for [`CohCarrier.GammaH M ⊤`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb Z)$ obtained from the full unit group of $\mathbb Z/M$, let $H^1(M) =$ [`CohCarrier.H1 M ⊤ 𝒪`](def/CohCarrier_Level.html#L162) be the $\mathcal O$-module of additive homomorphisms from $\Gamma_0(M)$ (written additively) to $\mathcal O$, and let $H^1_{\mathrm{par}}(M) =$ [`ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪`](def/ModularCurve_PeriodMap.html#L62) be its submodule of those homomorphisms vanishing on the elements singled out by the predicate [`ModularCurve.Period.IsParabolicHom`](def/ModularCurve_PeriodMap.html#L15). Then the family of $\mathcal O$-bilinear forms [`CuspForm.Bfam₀ 𝒪 M`](def/CuspForm_CornerPairingFamily.html#L140) on $H^1_{\mathrm{par}}(M)$, selected by Hilbert's choice operator from the predicate [`CuspForm.Bfam₀.Block 𝒪`](def/CuspForm_CornerPairingFamily.html#L117), satisfies that predicate, namely: (a) for every $M \neq 0$, the curried map $x \mapsto B_M(x, \cdot)$ from $H^1_{\mathrm{par}}(M)$ to its $\mathcal O$-dual is bijective; for every $\ell \neq 0$ and all $x, y, Tx, Ty \in H^1_{\mathrm{par}}(M)$ whose underlying characters satisfy $Tx =$ [`CohCarrier.heckeT M ⊤ ℓ 𝒪`](def/CohCarrier_Level.html#L250) $x$ and $Ty =$ `heckeT` $\,y$ (the transfer of the pullback along [`CohCarrier.conjL`](def/CohCarrier_Level.html#L228)), one has $B_M(Tx, y) = B_M(x, Ty)$; and for every $d \in (\mathbb Z/M)^{\times}$ and all $x, y, Dx, Dy \in H^1_{\mathrm{par}}(M)$ with $Dx =$ [`CohCarrier.diamondL M ⊤ 𝒪 d`](def/CohCarrier_Inst.html#L55) $x$ and $Dy =$ `diamondL` $\,y$ (pullback along conjugation by a chosen lift of $d$ to $\Gamma_0(M)$), one has $B_M(Dx, y) = B_M(x, Dy)$; (b) for all $M, M'$ with $M' \neq 0$ and all $d, d' \neq 0$, given [`CohCarrier.LevelLE M M' ⊤ ⊤ d`](def/CohCarrier_Level.html#L330) and `LevelLE M M' ⊤ ⊤ d'` (so $M \mid M'$ and $d, d' \mid M'/M$) together with $d d' = M'/M$, and given $x \in H^1_{\mathrm{par}}(M)$, $y \in H^1_{\mathrm{par}}(M')$, $ix \in H^1_{\mathrm{par}}(M')$ and $jy \in H^1_{\mathrm{par}}(M)$ whose underlying characters satisfy $ix =$ [`CohCarrier.iDegL`](def/CohCarrier_Level.html#L401) $\,x$ (pullback along the degree-$d$ map `iotaDeg`) and $jy =$ [`CohCarrier.jDegL`](def/CohCarrier_Level.html#L492) $\,y$ (the corestriction attached to the degree-$d'$ map), one has $B_M(jy, x) = B_{M'}(y, ix)$.
--
--   This is the pairing input of the Taylor–Wiles argument: classically $B_M(x,y) = x \cup w_M^{*} y$, the cup product on $H^1_{\mathrm{par}}$ twisted by the Atkin–Lehner involution, which is perfect, makes the Hecke and diamond operators self-adjoint and converts the two degeneracy maps between levels $M$ and $M'$ into adjoints of one another. It fixes the properties of the named family [`CuspForm.Bfam₀ 𝒪`](def/CuspForm_CornerPairingFamily.html#L140) and is used in the level-raising constructions [`CohCarrier.levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd`](thm.html#CohCarrier.levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd) and [`CohCarrier.levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comp_of_prime`](thm.html#CohCarrier.levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comp_of_prime), and in the corner-realization statement [`CuspForm.heckeLocal.selfAdjoint_and_bijective_and_finrank_eq_of_isCornerRealization_of_not_cube_dvd`](thm.html#CuspForm.heckeLocal.selfAdjoint_and_bijective_and_finrank_eq_of_isCornerRealization_of_not_cube_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_Bfam0_block.lean

import Definitions.Def_CuspForm_CornerPairingFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.Bfam0.block
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪)) :
    (∀ (M : ℕ) [NeZero M],
      Function.Bijective (CuspForm.Bfam₀ 𝒪 M) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (x y Tx Ty : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
          (Tx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 x →
          (Ty : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 y →
          CuspForm.Bfam₀ 𝒪 M Tx y = CuspForm.Bfam₀ 𝒪 M x Ty) ∧
      (∀ (d : (ZMod M)ˣ) (x y Dx Dy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
          (Dx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d x →
          (Dy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d y →
          CuspForm.Bfam₀ 𝒪 M Dx y = CuspForm.Bfam₀ 𝒪 M x Dy)) ∧
    (∀ (M M' : ℕ) [NeZero M'] (d d' : ℕ) [NeZero d] [NeZero d']
        (h : CohCarrier.LevelLE M M' ⊤ ⊤ d) (h' : CohCarrier.LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M)
        (x : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪))
        (y : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
        (ix : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
        (jy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
        (ix : CohCarrier.H1 M' ⊤ 𝒪) = CohCarrier.iDegL M M' ⊤ ⊤ d 𝒪 𝒪 h x →
        (jy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.jDegL M M' ⊤ ⊤ d' 𝒪 𝒪 h' y →
        CuspForm.Bfam₀ 𝒪 M jy x = CuspForm.Bfam₀ 𝒪 M' y ix) := by sorry
