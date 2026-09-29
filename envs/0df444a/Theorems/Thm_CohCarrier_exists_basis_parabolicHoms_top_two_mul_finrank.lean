-- Prove2me | Theorems.Thm_CohCarrier_exists_basis_parabolicHoms_top_two_mul_finrank
-- name    : CohCarrier.exists_basis_parabolicHoms_top_two_mul_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/74ae7a6d-ed42-5e9e-911a-228fd847fa72
-- title:
--   Parabolic homomorphism lattice for Γ₀(N): free of rank 2dim S₂
-- statement:
--   Let $N$ be a natural number that is nonzero, and write $\Gamma =$ [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image under the inclusion $\Gamma_0(N)\hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of the full subgroup of $(\mathbb{Z}/N)^\times$ under the character $\gamma\mapsto \bar d$ on $\Gamma_0(N)$. For a coefficient ring $R$, [`ModularCurve.Period.parabolicHoms R Γ R`](def/ModularCurve_PeriodMap.html#L62) denotes the $R$-submodule of additive homomorphisms $\varphi\colon \mathrm{Additive}\,\Gamma \to R$ that vanish on every $\gamma\in\Gamma$ whose underlying integral matrix satisfies $(\mathrm{tr}\,\gamma)^2 = 4$; put $d = \dim_{\mathbb{C}} S_2(\Gamma_0(N))$, the complex dimension of the space of weight-$2$ cusp forms for $\Gamma_0(N)$. The assertion is that there exists a $\mathbb{Z}$-basis $b$ of `parabolicHoms ℤ Γ ℤ` indexed by $\mathrm{Fin}(2d)$ with the following property: for every commutative ring $R$ (in the lowest universe) whose additive group is torsion-free, there is an $R$-basis $b^R$ of `parabolicHoms R Γ R`, indexed by the same $\mathrm{Fin}(2d)$, such that for each $i$ the homomorphism $b^R_i\colon \mathrm{Additive}\,\Gamma\to R$ equals $b_i$ followed by the canonical additive map $\mathbb{Z}\to R$.
--
--   This is the integral (and base-changeable) structure of the parabolic cohomology of $\Gamma_0(N)$ in weight $2$, with the rank pinned down by the Eichler–Shimura isomorphism: the lattice of parabolic homomorphisms over $\mathbb{Z}$ is free of rank $2\dim_{\mathbb{C}} S_2(\Gamma_0(N))$ and its basis remains a basis after scalar extension to any torsion-free coefficient ring. It supplies the free integral carrier on which the Hecke modules used in the modularity-lifting argument are built, and is used in computing ranks of corner submodules and in comparisons of Hecke operators at different levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_basis_parabolicHoms_top_two_mul_finrank.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.NumberTheory.ModularForms.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_basis_parabolicHoms_top_two_mul_finrank (N : ℕ) [NeZero N] :
    ∃ b : Module.Basis (Fin (2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) ℤ
        ↥(ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊤) ℤ),
      ∀ (R : Type) [CommRing R] [IsAddTorsionFree R],
        ∃ bR : Module.Basis (Fin (2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) R
            ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH N ⊤) R),
          ∀ i, (bR i : CohCarrier.H1 N ⊤ R) = (Int.castAddHom R).comp (b i : CohCarrier.H1 N ⊤ ℤ) := by sorry
