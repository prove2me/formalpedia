-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_isProper_zb
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlue.isProper_zb
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/e18c97eb-053f-576d-aa67-cd555b2a322d
-- title:
--   Properness of the glued Mumford levels over 𝒪/πⁿ⁺¹
-- statement:
--   Fix a prime number $r$ and a commutative domain $\mathcal O$ together with the hypothesis that it is a discrete valuation ring, an irreducible element $\pi \in \mathcal O$ whose residue ring $\mathcal O/(\pi)$ has cardinality exactly $r$, and a field $K₀$ which is an $\mathcal O$-algebra and a fraction field of $\mathcal O$. Let $g₁ \in \mathrm{GL}_2(K₀)$ be the element whose underlying matrix is $\mathrm{diag}(\pi, 1)$ (with $\pi$ taken in $K₀$ through the structure map), and let $N$ be a subgroup of $\mathrm{PGL}(2, K₀)$. Let $Gl$ be a term of the structure `MumfordGlue` for these data: a tower of schemes $Z_n$ with morphisms $zb_n : Z_n \to \operatorname{Spec}(\mathcal O/(\pi^{n+1}))$ and transition morphisms $zt_n : Z_n \to Z_{n+1}$ making each square over the truncation maps $\mathcal O/(\pi^{n+2}) \to \mathcal O/(\pi^{n+1})$ cartesian, with each $zb_n$ flat and separated, together with charts $\zeta_{h,n}$ from the spectra of $(\mathrm{chartERing}\ \mathcal O\ \pi\ r)/(\pi^{n+1})$, where $\mathrm{chartERing}$ is the localisation of the edge-quotient ring away from its discriminant, these charts being open immersions over the base, compatible with the tower, covering $Z_n$ by finitely many of them, invariant under left translation by elements of $\mathrm{GL}_2(K₀)$ landing in $N$, and subject to the stated gluing relations expressed through Deligne data on $\mathcal O$-algebras. The conclusion is that for every natural number $n$ the morphism $zb_n$ is proper.
--
--   This is the properness of each level of the Mumford-style glued formal scheme over the truncated base $\mathcal O/\pi^{n+1}$, in the Čerednik–Drinfeld description of the $p$-adic upper half plane. It is used in the construction of proper affine neighbourhoods on the levels and in the combined properness statement for the tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_isProper_zb.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlue.isProper_zb
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    :
    ∀ n : ℕ, IsProper (Gl.zb n) := by sorry
