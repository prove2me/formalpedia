-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaTypeLocally_of_isPullback_of_faithfullyFlat_etale
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.thetaTypeLocally_of_isPullback_of_faithfullyFlat_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/fcdde87c-85a6-59e7-a8b4-f18b6be6ca07
-- title:
--   Descent of étale-local theta type along faithfully flat étale maps
-- statement:
--   Fix natural numbers $g$, $N$, $n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta(i)$ nonzero. Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra which is faithfully flat and étale over $S$. Let $u$ be a polarised abelian scheme of parameters $(g, N+1, n)$ over $S$ — a scheme $A$ over $\operatorname{Spec} S$ with a commutative relative group law, the abelian-scheme property bundle, all fibres of topological Krull dimension $g$, a list $P_0,\dots,P_{2g-1}$ of $n$-torsion sections that are independent and generate the $n$-torsion on geometric fibres, and an invertible module `pol` which is very ample in the sense of admitting a Proj presentation that is a closed immersion and whose geometric fibrewise $H^0$ has rank $N+1$ — and let $u'$ be such a datum over $S'$. Assume $h$: $u'$ is the base change of $u$ along $S \to S'$, i.e. there is a morphism $u'.A \to u.A$ forming a pullback square over $\operatorname{Spec} S' \to \operatorname{Spec} S$ which is compatible with the two group laws, carries each marked section $P_i$ of $u'$ to the base change of the corresponding section of $u$, and along which `pol` of $u$ pulls back to an isomorphic copy of `pol` of $u'$. Assume further that $u'$ has the property `ThetaTypeLocally` for $\delta$ over $S'$: for every $S'$-algebra $R$ and every $\zeta \in R$ with $\zeta^{N+1} = 1$ and $1 - \zeta^{j}$ a unit for all $0 < j < N+1$, there exist a commutative $R$-algebra $R'$ that is faithfully flat and étale over $R$, a framed polarised abelian scheme $X'$ over $R'$ (a polarised abelian scheme together with a Proj presentation of its polarisation module by $N+1$ sections which is a closed immersion and whose sections form a section basis), and a bijection $e : \mathrm{Fin}(N+1) \simeq \prod_i \mathbb{Z}/\delta(i)$, such that $X'$ is the base change of $u'$ along $S' \to R \to R'$ and $X'$ is theta-adapted for $\delta$ and $e$, meaning that there is a Schrödinger frame for the data $(X'.f, X'.L, X'.\mathrm{pol}, \delta)$ whose section indexed by $e(i)$ is the pullback of the $i$-th frame section. The conclusion is that $u$ itself has the property `ThetaTypeLocally` for $\delta$ over $S$.
--
--   This is the descent step showing that the étale-local theta-structure condition on a polarised abelian scheme is insensitive to faithfully flat étale base change of the base ring, so that it can be imposed as a property of a moduli problem rather than of a chosen base. It is used in the construction of fine moduli for polarised abelian schemes of theta type $\delta$, including the quasi-projectivity statement, and in the invariance of the condition under isomorphism of polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaTypeLocally_of_isPullback_of_faithfullyFlat_etale.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.thetaTypeLocally_of_isPullback_of_faithfullyFlat_etale
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)]
    {S : Type} [CommRing S] (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S'] [Algebra.Etale S S']
    (u : PolarisedAbelianScheme g (N + 1) n S) (u' : PolarisedAbelianScheme g (N + 1) n S')
    (h : PolarisedAbelianScheme.IsPullback (algebraMap S S') u u') (hu' : PolarisedAbelianScheme.ThetaTypeLocally δ S' u') :
    PolarisedAbelianScheme.ThetaTypeLocally δ S u := by sorry
