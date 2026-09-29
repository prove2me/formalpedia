-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_locallyOfFiniteType_and_quasiCompact
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlue.locallyOfFiniteType_and_quasiCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/b64b71f8-a5b2-5c01-8ab1-d2e30c4eb711
-- title:
--   Mumford levels are locally of finite type and quasi-compact
-- statement:
--   Fix a prime $r$, a commutative domain $\mathcal{O}$ carrying a discrete valuation ring structure, an irreducible element $\pi \in \mathcal{O}$ whose residue ring $\mathcal{O}/(\pi)$ has cardinality $r$, a fraction field $K_0$ of $\mathcal{O}$, an element $g_1 \in \mathrm{GL}_2(K_0)$ whose matrix is $\mathrm{diag}(\pi, 1)$, and a subgroup $N \le \mathrm{PGL}_2(K_0)$. Let $Gl$ be a `MumfordGlue` datum for these data: a family of schemes $Z_n$ with structure morphisms $\mathtt{zb}\,n : Z_n \to \operatorname{Spec}(\mathcal{O}/(\pi^{n+1}))$, flat and separated, transition maps $\mathtt{zt}\,n : Z_n \to Z_{n+1}$ exhibiting each level as the pullback of the next along the base truncation, together with charts $\zeta_{h,n} : \operatorname{Spec}\bigl(\mathtt{chartERing}\,\mathcal{O}\,\pi\,r / (\pi^{n+1})\bigr) \to Z_n$ indexed by $h \in \mathrm{GL}_2(K_0)$, which are open immersions over the base, compatible with the transitions, invariant under left multiplication by elements of $N$, satisfy the Deligne-datum gluing relations, and are such that for each $n$ finitely many of them cover $Z_n$. The conclusion is that for every $n$ the morphism $\mathtt{zb}\,n$ is locally of finite type and quasi-compact.
--
--   This is the finiteness half of the basic geometric properties of the levels of Mumford's formal scheme over $\mathcal{O}$ in the Čerednik–Drinfeld uniformisation: together with flatness, separatedness and the properness criterion it makes $Z_n$ an admissible formal model. It is used downstream in the construction of an affine neighbourhood of a point, in the proof that $\mathtt{zb}\,n$ is proper, and in the analysis of the special level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_locallyOfFiniteType_and_quasiCompact.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlue.locallyOfFiniteType_and_quasiCompact
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    :
    ∀ n : ℕ, LocallyOfFiniteType (Gl.zb n) ∧ QuasiCompact (Gl.zb n) := by sorry
