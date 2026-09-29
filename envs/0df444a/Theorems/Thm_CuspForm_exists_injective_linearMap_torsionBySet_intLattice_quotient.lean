-- Prove2me | Theorems.Thm_CuspForm_exists_injective_linearMap_torsionBySet_intLattice_quotient
-- name    : CuspForm.exists_injective_linearMap_torsionBySet_intLattice_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/a82f06fa-0460-53fe-b297-928c37def5cb
-- title:
--   𝔪-torsion in L/pL embeds into T/𝔪
-- statement:
--   Let $N$ be a nonzero natural number and $p$ a natural number, and write $\mathbb T$ for [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14), the polynomial ring $\mathbb Z[x_\ell : \ell \text{ prime}]$ on the set of primes. Let $\mathfrak m \subset \mathbb T$ be a maximal ideal containing the constant $p$, and put $k = \mathbb T/\mathfrak m$. Let $L =$ [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3) be the $\mathbb Z$-submodule of weight-two cusp forms on $\Gamma_0(N)$ spanned by those forms all of whose $q$-expansion coefficients $a_n$ are rational integers. Then $L$ is a $\mathbb T$-module through [`CuspForm.latticeHeckeFamily N`](def/CuspForm_LatticeHeckeFamily.html#L13): the variable attached to a prime $\ell$ acts by the restriction to $L$ of the Hecke operator $U_\ell$ when $\ell \mid N$ and of $T_\ell$ when $\ell \nmid N$, and a general polynomial acts by evaluating it at these commuting endomorphisms. The assertion is that the $\mathfrak m$-torsion submodule of $L/\bigl((p)\cdot L\bigr)$, consisting of the classes annihilated by every element of $\mathfrak m$ and hence a $k$-vector space, admits an injective $k$-linear map into $k$ itself.
--
--   This is the mod $\mathfrak m$ form of the duality, going back to Mazur, between the Hecke algebra and cusp forms with integral $q$-expansion: pairing a form with a Hecke operator through the first $q$-coefficient shows that the $\mathfrak m$-torsion of $L/pL$ is at most one-dimensional over the residue field. It is used in the bound on the Dieudonné module of the $\mathfrak m$-torsion in the local–local case, [`ModularCurve.natCard_dieudonneModule_quot_range_verschiebung_le_of_local_local_model_heckeTorsion_jZero`](thm.html#ModularCurve.natCard_dieudonneModule_quot_range_verschiebung_le_of_local_local_model_heckeTorsion_jZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_injective_linearMap_torsionBySet_intLattice_quotient.lean

import Definitions.Def_CuspForm_LatticeHeckeFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_injective_linearMap_torsionBySet_intLattice_quotient (N p : ℕ) [NeZero N]
    (m : Ideal ModularCurve.HeckeAlg) [m.IsMaximal] (hpm : ((p : ℕ) : ModularCurve.HeckeAlg) ∈ m) :
    letI := (CuspForm.latticeHeckeFamily N).module
    ∃ a : Submodule.torsionBySet ModularCurve.HeckeAlg
        (↥(CuspForm.intLattice N 2) ⧸ (Ideal.span {((p : ℕ) : ModularCurve.HeckeAlg)} • (⊤ : Submodule ModularCurve.HeckeAlg ↥(CuspForm.intLattice N 2)))) m
          →ₗ[ModularCurve.HeckeAlg ⧸ m] (ModularCurve.HeckeAlg ⧸ m),
      Function.Injective a := by sorry
