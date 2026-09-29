-- Prove2me | Theorems.Thm_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms
-- name    : CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/54235b78-c7f6-5ab2-bf28-1e282e610bb5
-- title:
--   Perfect Hecke-self-adjoint degeneracy-compatible pairings on parabolic homomorphisms
-- statement:
--   Let $\mathcal{O}$ be a local integral domain of characteristic zero and let $p$ be an odd prime that is not a unit in $\mathcal{O}$. The assertion is the existence of a single family $B$, indexed by all $M : \mathbb{N}$, of $\mathcal{O}$-bilinear maps $B_M$ on the $\mathcal{O}$-module $\mathtt{parabolicHoms}\,\mathcal{O}\,(\mathtt{GammaH}\,M\,\top)\,\mathcal{O}$ — the submodule of those additive homomorphisms $\varphi$ from the additivisation of $\Gamma_0(M)$, viewed as the subgroup `GammaH M ⊤` of $\mathrm{SL}_2(\mathbb{Z})$, to $\mathcal{O}$ that vanish on every element whose matrix trace squared equals $4$ — with the following properties. First, for every $M \neq 0$: the map $x \mapsto B_M(x,-)$ is a bijection onto the full $\mathcal{O}$-dual, so $B_M$ is perfect; for every $\ell \neq 0$ and all parabolic $x, y, Tx, Ty$ whose underlying homomorphisms satisfy $Tx = \mathtt{heckeT}\,M\,\top\,\ell\,\mathcal{O}\,x$ and $Ty = \mathtt{heckeT}\,M\,\top\,\ell\,\mathcal{O}\,y$ (the transfer of the restriction along conjugation by the upper degeneracy matrix) one has $B_M(Tx, y) = B_M(x, Ty)$; and the same adjunction holds with `heckeT` replaced by $\mathtt{diamondL}\,M\,\top\,\mathcal{O}\,d$, precomposition with conjugation by a chosen lift of $d \in (\mathbb{Z}/M)^\times$ to $\Gamma_0(M)$, for every such $d$. Second, for all $M$ and $M' \neq 0$, all $d, d' \neq 0$ with $\mathtt{LevelLE}\,M\,M'\,\top\,\top\,d$ and $\mathtt{LevelLE}\,M\,M'\,\top\,\top\,d'$ (so $M \mid M'$ and $d, d' \mid M'/M$) and $d d' = M'/M$, and all parabolic $x$ at level $M$, $y$ at level $M'$, $ix$ at level $M'$ with underlying homomorphism $\mathtt{iDegL}\,M\,M'\,\top\,\top\,d\,\mathcal{O}\,\mathcal{O}\,h\,x$ (pullback along $\mathtt{iotaDeg}$) and $jy$ at level $M$ with underlying homomorphism $\mathtt{jDegL}\,M\,M'\,\top\,\top\,d'\,\mathcal{O}\,\mathcal{O}\,h'\,y$ (the corresponding transfer), one has $B_M(jy, x) = B_{M'}(y, ix)$. The Hecke, diamond and degeneracy clauses are phrased through explicit parabolic witnesses for the images rather than by asserting that the operators preserve parabolicity.
--
--   This is the Poincaré-duality pairing on the parabolic cohomology of the modular curves of level $\Gamma_0(M)$ with coefficients in $\mathcal{O}$, in the twisted form for which the Hecke and diamond operators are self-adjoint and the two degeneracy maps between levels $M$ and $M'$ are mutually adjoint. It is used to produce the duality underlying the pairing on the relevant Hecke-module blocks, and is cited by [`CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_map_iDegL_parabolicHoms`](thm.html#CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_map_iDegL_parabolicHoms) and by [`CuspForm.Bfam0.block`](thm.html#CuspForm.Bfam0.block).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.lean

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪)) :
    ∃ B : (M : ℕ) → ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪]
        ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪] 𝒪,
      (∀ (M : ℕ) [NeZero M],
        Function.Bijective (B M) ∧
        (∀ (ℓ : ℕ) [NeZero ℓ] (x y Tx Ty : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
            (Tx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 x →
            (Ty : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 y → B M Tx y = B M x Ty) ∧
        (∀ (d : (ZMod M)ˣ) (x y Dx Dy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
            (Dx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d x →
            (Dy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d y → B M Dx y = B M x Dy)) ∧
      (∀ (M M' : ℕ) [NeZero M'] (d d' : ℕ) [NeZero d] [NeZero d']
          (h : CohCarrier.LevelLE M M' ⊤ ⊤ d) (h' : CohCarrier.LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M)
          (x : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪))
          (y : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
          (ix : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
          (jy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
          (ix : CohCarrier.H1 M' ⊤ 𝒪) = CohCarrier.iDegL M M' ⊤ ⊤ d 𝒪 𝒪 h x →
          (jy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.jDegL M M' ⊤ ⊤ d' 𝒪 𝒪 h' y →
          B M jy x = B M' y ix) := by sorry
