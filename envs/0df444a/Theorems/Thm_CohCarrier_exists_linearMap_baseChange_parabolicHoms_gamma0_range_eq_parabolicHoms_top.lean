-- Prove2me | Theorems.Thm_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top
-- name    : CohCarrier.exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/ce9e8696-8fd1-5ad0-902c-72ec2f433b44
-- title:
--   Base change of the parabolic lattice of Γ₀(N)
-- statement:
--   Let $N \ge 1$ and let $\mathcal{O}$ be a commutative ring whose additive group is torsion-free. Write $P =$ `parabolicHoms ℤ (Gamma0 N) ℤ` for the submodule of additive homomorphisms $x \colon \mathrm{Additive}\,\Gamma_0(N) \to \mathbb{Z}$ that vanish on every $\gamma$ whose matrix has $\mathrm{tr}(\gamma)^2 = 4$, and let $\Gamma_H =$ [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133) be the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained from the full subgroup $H = \top \le (\mathbb{Z}/N)^\times$, so that $\Gamma_H \le \Gamma_0(N)$, and [`CohCarrier.H1 N ⊤ 𝒪`](def/CohCarrier_Level.html#L162) $= \mathrm{Hom}(\mathrm{Additive}\,\Gamma_H, \mathcal{O})$. The assertion is that there exists an $\mathcal{O}$-linear map $\iota \colon \mathcal{O} \otimes_{\mathbb{Z}} P \to \mathrm{Hom}(\mathrm{Additive}\,\Gamma_H, \mathcal{O})$ such that: (i) for all $r \in \mathcal{O}$, $x \in P$ and $\gamma \in \Gamma_H$, $\iota(r \otimes x)(\gamma) = r \cdot x(\gamma)$, the integer $x(\gamma)$ being taken along $\Gamma_H \le \Gamma_0(N)$ and mapped into $\mathcal{O}$; (ii) $\iota$ is injective; (iii) the range of $\iota$ is exactly `parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪`, the homomorphisms $\Gamma_H \to \mathcal{O}$ vanishing on all elements of squared trace $4$; and (iv) for every $\ell \ge 1$, every $r \in \mathcal{O}$ and all $x, y \in P$ with $y =$ [`ModularCurve.PDPairing.heckeT0 N ℓ ℤ`](def/ModularCurve_PDPairing.html#L363) $x$, one has $\iota(r \otimes y) =$ [`CohCarrier.heckeT N ⊤ ℓ 𝒪`](def/CohCarrier_Level.html#L250) $(\iota(r \otimes x))$, both Hecke operators being the transfer maps attached to conjugation by the upper-triangular matrix determined by $\ell$.
--
--   This is the comparison between the integral parabolic lattice $H^1_{\mathrm{par}}(\Gamma_0(N), \mathbb{Z})$, on which the cup-product pairing of the modular curve is defined, and the parabolic part of the cohomological carrier $\mathrm{Hom}(\Gamma_H, \mathcal{O})$ with coefficients in a torsion-free ring, together with compatibility of the two transfer Hecke operators. It is used to transport bilinear and Hecke structure from the lattice to the carrier, and is cited by [`ModularCurve.exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms`](thm.html#ModularCurve.exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PDPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CongruenceSubgroup ModularCurve.Period

theorem CohCarrier.exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top
    (N : ℕ) [NeZero N] (𝒪 : Type) [CommRing 𝒪] [IsAddTorsionFree 𝒪] :
    ∃ ι : 𝒪 ⊗[ℤ] ↥(parabolicHoms ℤ (Gamma0 N) ℤ) →ₗ[𝒪] CohCarrier.H1 N ⊤ 𝒪,
      (∀ (r : 𝒪) (x : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)) (γ : ↥(CohCarrier.GammaH N ⊤)),
          ι (r ⊗ₜ[ℤ] x) (Additive.ofMul γ) =
            r * ((x : Additive ↥(Gamma0 N) →+ ℤ)
              (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) : 𝒪)) ∧
      Function.Injective ι ∧
      LinearMap.range ι = parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (r : 𝒪) (x y : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)),
        (y : Additive ↥(Gamma0 N) →+ ℤ) =
            ModularCurve.PDPairing.heckeT0 N ℓ ℤ (x : Additive ↥(Gamma0 N) →+ ℤ) →
          ι (r ⊗ₜ[ℤ] y) = CohCarrier.heckeT N ⊤ ℓ 𝒪 (ι (r ⊗ₜ[ℤ] x)) := by sorry
