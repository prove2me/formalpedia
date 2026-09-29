-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_zero
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlue.affineNbhd_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/a75958a1-4d2d-5c10-8653-72c4ce11db4e
-- title:
--   Finite sets in the special level lie in an affine open
-- statement:
--   Fix a prime $r$ and a discrete valuation ring $\mathcal O$ (a commutative domain with the discrete valuation property `hdvr`) together with an irreducible element $\pi$ whose residue ring $\mathcal O/(\pi)$ has exactly $r$ elements, and a field $K₀$ which is an $\mathcal O$-algebra and a fraction field of $\mathcal O$. Let $g₁ \in \mathrm{GL}_2(K₀)$ be the diagonal matrix $\mathrm{diag}(\pi,1)$ (with $\pi$ mapped into $K₀$), let $N$ be a subgroup of $\mathrm{PGL}_2(K₀)$, and let `Gl` be a term of the structure `MumfordGlue` for these data: that is, a family of schemes $Z_n$ with structure morphisms $zb_n : Z_n \to \operatorname{Spec}(\mathcal O/(\pi^{n+1}))$ that are flat and separated, transition morphisms $zt_n : Z_n \to Z_{n+1}$ exhibiting each $Z_n$ as the pullback of $Z_{n+1}$ along the reduction $\operatorname{Spec}(\mathcal O/(\pi^{n+1})) \to \operatorname{Spec}(\mathcal O/(\pi^{n+2}))$, and charts $\zeta_{h,n}$, indexed by $h \in \mathrm{GL}_2(K₀)$, from the spectrum of $(\text{chartERing }\mathcal O\,\pi\,r)/(\pi^{n+1})$ — the localisation of the edge ring away from its discriminant, reduced modulo $\pi^{n+1}$ — into $Z_n$, which lie over the base, are compatible with the $zt_n$, are open immersions, cover each $Z_n$ by finitely many of them, are invariant under left translation of $h$ by elements of $N$, and satisfy the moduli relation `ζ_rel` comparing chart coordinates with Deligne data of lines on base-changed full lattices. Then for every finite subset $S$ of the underlying space of $Z_0$ there is an open subset $U$ of $Z_0$ which is an affine open and contains $S$.
--
--   This is the affine-neighbourhood property of the special level $Z_0$ of a Mumford glue datum: the reduced special fibre of the Drinfel'd-type formal scheme, a curve over the residue field $\mathcal O/(\pi)$, has enough affine opens to engulf any finite set of points. It is used, together with properness of the structure morphisms, in [`CerednikDrinfeld.FormalOmega.MumfordGlue.isProper_and_affineNbhd`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlue.isProper_and_affineNbhd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_zero.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlue.affineNbhd_zero
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    (S : Set (Gl.Z 0)) (hS : S.Finite) :
    ∃ U : (Gl.Z 0).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Gl.Z 0)) := by sorry
