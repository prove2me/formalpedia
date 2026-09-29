-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_of_affineNbhd_zero
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlue.affineNbhd_of_affineNbhd_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/c53aa47a-bf1a-579a-8592-6d131f7d3358
-- title:
--   Affine neighbourhoods propagate up a Mumford glue tower
-- statement:
--   Fix a prime $r$ and a commutative domain $\mathcal{O}$ which is a discrete valuation ring, with an irreducible element $\pi$ such that the residue ring $\mathcal{O}/(\pi)$ has cardinality $r$; let $K_0$ be a field which is a fraction field of $\mathcal{O}$, let $g_1 \in \mathrm{GL}_2(K_0)$ be the diagonal matrix $\mathrm{diag}(\pi, 1)$ (with $\pi$ taken in $K_0$ via the structure map), and let $N$ be a subgroup of $\mathrm{PGL}_2(K_0)$. Let $Gl$ be a term of `MumfordGlue` for these data: it consists of schemes $Z_n$ together with structure morphisms $zb_n : Z_n \to \operatorname{Spec}(\mathcal{O}/(\pi^{n+1}))$ and transition morphisms $zt_n : Z_n \to Z_{n+1}$ such that each square formed by $zt_n$, $zb_n$, $zb_{n+1}$ and the morphism $\operatorname{Spec}(\mathcal{O}/(\pi^{n+1})) \to \operatorname{Spec}(\mathcal{O}/(\pi^{n+2}))$ induced by the quotient factor map is cartesian, each $zb_n$ being flat and separated, together with open-immersion charts $\zeta_{h,n}$ from $\operatorname{Spec}$ of the localisation `chartERing` modulo $\pi^{n+1}$, indexed by $h \in \mathrm{GL}_2(K_0)$, their compatibilities with $zb$ and $zt$, a finite covering property at each level, invariance under $N$, and the relations to Deligne data — these remaining components are summarised here. Assume that every finite subset of $Z_0$ is contained in an affine open of $Z_0$. Then, for every $n$, every finite subset of $Z_n$ is contained in an affine open of $Z_n$.
--
--   This is the propagation of the property 'every finite set of points lies in an affine open' up the tower of infinitesimal levels of a Mumford glue datum, the tower being an $\mathcal{O}/(\pi^{n+1})$-thickening of its special level. It feeds into the proof that the glued formal scheme is proper and has this affine-neighbourhood property at every level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_of_affineNbhd_zero.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlue.affineNbhd_of_affineNbhd_zero
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    (h0 : ∀ S : Set (Gl.Z 0), S.Finite → ∃ U : (Gl.Z 0).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Gl.Z 0))) :
    ∀ (n : ℕ) (S : Set (Gl.Z n)), S.Finite → ∃ U : (Gl.Z n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Gl.Z n)) := by sorry
