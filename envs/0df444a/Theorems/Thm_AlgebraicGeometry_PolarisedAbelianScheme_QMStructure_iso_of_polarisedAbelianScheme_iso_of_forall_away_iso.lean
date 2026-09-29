-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_iso_of_polarisedAbelianScheme_iso_of_forall_away_iso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_polarisedAbelianScheme_iso_of_forall_away_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/42c5bd45-a33c-503f-8e0e-d5f9214a5e92
-- title:
--   From a polarised isomorphism to a QM isomorphism, locally
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a map $star \colon \Lambda \to \Lambda$, and $\beta \colon \mathrm{Fin}\,4 \to \Lambda$, together with naturals $d$ and $m$ with $3 \le m$, and a commutative ring $S$ in which the image of $m$ is a unit. Let $X, X'$ be polarised abelian schemes over $S$ of relative dimension $2$ with full $m$-torsion basis of $4$ sections and invertible, very ample sheaf of geometric fibre $H^0$-rank $d$, and let $t$ on $X$ and $t'$ on $X'$ be QM structures: $\Lambda$-actions by endomorphisms over $S$ that are additive, satisfy $\mathrm{act}(xy) = \mathrm{act}(y) \circ \mathrm{act}(x)$, obey the trace condition attached to $star$, carry a section $P$ with $\mathrm{act}(\beta_j)(P) = X.P_j$, and admit a canonical polarisation datum whose triple tensor power is locally on the base isomorphic to the given sheaf. Let $r \colon \mathrm{Fin}\,k \to S$ have $(r_0,\dots,r_{k-1}) = (1)$, and for each $i$ let $(Xl_i, tl_i)$ and $(Xl'_i, tl'_i)$ be such data over $S[1/r_i]$ which are pullbacks of $(X,t)$, resp. $(X',t')$, along $S \to S[1/r_i]$, in the sense that there is a morphism on total spaces making a pullback square over $\mathrm{Spec}$ of the structure map, compatible with the relative group laws on points, the level sections, the polarisations up to isomorphism of pullbacks, the $\Lambda$-actions and the distinguished points. Assume that for every $i$ the pairs $(Xl_i, tl_i)$ and $(Xl'_i, tl'_i)$ are QM-isomorphic, and that $X$ and $X'$ are isomorphic as polarised abelian schemes with level structure. Then $t$ and $t'$ are QM-isomorphic: there is an isomorphism $X.A \cong X'.A$ over $S$ compatible with the group laws, matching the level sections, identifying the polarisations locally on the base, intertwining the two $\Lambda$-actions and carrying $t.P$ to $t'.P$.
--
--   This is the rigidity step by which an isomorphism of the underlying polarised abelian surfaces with level structure, refined over a standard affine cover by isomorphisms respecting the quaternionic multiplication, is recognised as a single global isomorphism of QM data; the hypothesis $3 \le m$ with $m$ invertible supplies the rigidity through the uniqueness statement [`AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le_of_locally`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le_of_locally). It feeds [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_forall_away_iso`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_forall_away_iso), part of the relative representability of the moduli problem of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_iso_of_polarisedAbelianScheme_iso_of_forall_away_iso.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_polarisedAbelianScheme_iso_of_forall_away_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ}
    {d m : ℕ} (hm : 3 ≤ m) {S : Type} [CommRing S] (hm' : IsUnit ((m : ℕ) : S))
    {X X' : PolarisedAbelianScheme 2 d m S} (t : QMStructure Λ star β X) (t' : QMStructure Λ star β X')
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (Xl : ∀ i, PolarisedAbelianScheme 2 d m (Localization.Away (r i)))
    (tl : ∀ i, QMStructure Λ star β (Xl i))
    (Xl' : ∀ i, PolarisedAbelianScheme 2 d m (Localization.Away (r i)))
    (tl' : ∀ i, QMStructure Λ star β (Xl' i))
    (ht : ∀ i, QMStructure.IsPullback (algebraMap S (Localization.Away (r i))) t (tl i))
    (ht' : ∀ i, QMStructure.IsPullback (algebraMap S (Localization.Away (r i))) t' (tl' i))
    (hloc : ∀ i, QMStructure.Iso (tl i) (tl' i))
    (hX : PolarisedAbelianScheme.Iso X X') :
    QMStructure.Iso t t' := by sorry
