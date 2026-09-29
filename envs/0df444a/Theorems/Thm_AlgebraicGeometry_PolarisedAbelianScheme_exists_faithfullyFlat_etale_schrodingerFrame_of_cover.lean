-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_etale_schrodingerFrame_of_cover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/a0e79dd3-ae1c-566c-8bc4-90b14ff9b620
-- title:
--   Étale absorption of Schrödinger frames along a basic-open cover
-- statement:
--   Fix natural numbers $g,d,n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with nonzero entries, and let $S$ be a commutative ring carrying a term $u$ of `PolarisedAbelianScheme g d n S`: a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law $L$ on the functor of points of $f$, the property bundle of an abelian scheme, all fibres of topological Krull dimension $g$, sections $P_1,\dots,P_{2g}$ killed by $n$ which form a basis of the $n$-torsion of every geometric fibre, and an invertible $A$-module `pol` that is a closed immersion by sections over $f$ with $\dim_k H^0 = d$ on every geometric fibre. Let $S_1$ be a faithfully flat étale $S$-algebra, let $r_1,\dots,r_m \in S_1$ generate the unit ideal, and suppose that for each $j$ there is given a Schrödinger frame of type $\delta$ for $(f, L, \mathtt{pol})$ over the base change of $\operatorname{Spec} S$ along $S \to S_1 \to S_1[1/r_j]$ — that is, sections $\sigma_h$ of the pulled-back line bundle indexed by $H(\delta) = \prod_i \mathbb{Z}/\delta_i$ forming a basis of the global sections over the base ring, together with theta points lifting each $h \in H(\delta)$ and each additive character of $H(\delta)$, acting on the $\sigma_h$ by translation $\sigma_h \mapsto \sigma_{h+h'}$ and by scaling by $\chi(h)$ respectively. Then there exists a commutative ring $S'$ with an $S$-algebra structure which is faithfully flat and étale over $S$ and for which a Schrödinger frame of type $\delta$ for $(f, L, \mathtt{pol})$ over $\operatorname{Spec} S' \to \operatorname{Spec} S$ exists. The conclusion asserts only non-emptiness; no relation between $S'$ and $S_1$ is recorded.
--
--   This is the absorption step in the construction of theta (Schrödinger) structures of Mumford's type: frames existing only locally on a basic-open cover of one faithfully flat étale base change are replaced by a single frame over one faithfully flat étale $S$-algebra, obtained by taking the product over the cover. It is used by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_schrodingerFrame_of_rootedSymmetricOfType`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_schrodingerFrame_of_rootedSymmetricOfType), and the transport of theta points across the resulting decomposition rests on the two cited results about theta points under idempotent decompositions and under pullback squares.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_etale_schrodingerFrame_of_cover
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)]
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    (S₁ : Type) [CommRing S₁] [Algebra S S₁] [Module.FaithfullyFlat S S₁] [Algebra.Etale S S₁]
    (m : ℕ) (r : Fin m → S₁) (hr : Ideal.span (Set.range r) = ⊤)
    (F : ∀ j : Fin m, SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom ((algebraMap S₁ (Localization.Away (r j))).comp (algebraMap S S₁)))) δ) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧ Algebra.Etale S S' ∧
      Nonempty (SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S S'))) δ) := by sorry
