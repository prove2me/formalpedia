-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_rosatiCompatible_tensor_pullback_negMor_of_kernelTrivial_of_isArtinianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_rosatiCompatible_tensor_pullback_negMor_of_kernelTrivial_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/a9f8fe76-eb4d-52ad-9544-d664f2020bc7
-- title:
--   Rosati compatibility descends from the symmetrisation of L
-- statement:
--   Fix rationals $a,b$, a subgroup $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ (an additive $\mathbb{Z}$-submodule of the quaternion algebra), a natural number $N$, and a commutative ring $S$ that is local, Noetherian and Artinian with algebraically closed residue field. Let $E$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $S$: a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} S$, a commutative relative group law $E.L$ on the functor of points over $\operatorname{Spec} S$, an abelian-scheme property bundle, all fibres of topological Krull dimension $2$, an action $E.\mathrm{act} : \Lambda \to \operatorname{End}(E.A)$ by morphisms over $\operatorname{Spec} S$ compatible with the group law and with multiplication, addition and reduced traces in $\Lambda$, together with the remaining curve and level data. Let $\star : \Lambda \to \Lambda$ be an arbitrary map and let $\mathcal{L}$ be an invertible module on $E.A$, that is, one locally isomorphic to the unit module on a neighbourhood of each point. Write $\Lambda(\mathcal{M}) = m^{*}\mathcal{M} \otimes p_1^{*}\mathcal{M}^{\vee} \otimes p_2^{*}\mathcal{M}^{\vee}$ for the Mumford bundle of a module $\mathcal{M}$ on $E.A \times_{\operatorname{Spec} S} E.A$. Assume: (i) $\mathcal{L}$ has trivial kernel, i.e. for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every point $x$ of $E.A$ over $t$, if the restriction of $\Lambda(\mathcal{L})$ along the slice at $x$ is, locally on $\operatorname{Spec} R$, isomorphic to the unit module, then $x$ is the identity section $E.L.\mathrm{one}\,t$; and (ii) the symmetrisation $\mathcal{L} \otimes [-1]^{*}\mathcal{L}$, where $[-1]$ is the inversion morphism `negMor` of $E.L$, is Rosati-compatible with the $\Lambda$-action through $\star$. The conclusion is that $\mathcal{L}$ itself is Rosati-compatible: for every $x \in \Lambda$ the pullbacks of $\Lambda(\mathcal{L})$ along $1 \times \mathrm{act}(x)$ and along $\mathrm{act}(x^{\star}) \times 1$ are isomorphic locally on $\operatorname{Spec} S$.
--
--   This is the descent, over an Artin local base with algebraically closed residue field, of Rosati compatibility from the symmetrisation $\mathcal{L} \otimes [-1]^{*}\mathcal{L}$ to $\mathcal{L}$ itself, the step that rules out a residual two-torsion ambiguity by passing to the closed fibre and invoking torsion-freeness of the group of correspondences there. It feeds the construction of canonical polarisation data on fake elliptic curves over Artinian bases used in the Čerednik–Drinfel'd comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_rosatiCompatible_tensor_pullback_negMor_of_kernelTrivial_of_isArtinianRing.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra
  CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_rosatiCompatible_tensor_pullback_negMor_of_kernelTrivial_of_isArtinianRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
    (E : FakeEllipticCurve Λ N S) (star : ↥Λ → ↥Λ)
    (𝓛 : E.A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : KernelTrivial E.f E.L 𝓛)
    (hR : RosatiCompatible E.f E.L (𝓛 ⊗ (Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓛) E.act E.act_over star) :
    RosatiCompatible E.f E.L 𝓛 E.act E.act_over star := by sorry
