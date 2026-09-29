-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isPullback_isThetaAdapted_of_schrodingerFrame
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isPullback_isThetaAdapted_of_schrodingerFrame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/c9b010ea-75eb-51e8-a980-1ca6a9378aa7
-- title:
--   Theta-adapted framed base change from a Schrödinger frame
-- statement:
--   Fix natural numbers $g$, $N$, $n$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero, and a bijection $e$ between $\mathrm{Fin}(N+1)$ and $H(\delta) = \prod_i \mathbb{Z}/\delta_i$. Let $R$ be a commutative ring and $R'$ a commutative $R$-algebra. Let $u$ be a polarised abelian scheme of relative dimension $g$, polarisation degree $N+1$ and torsion level $n$ over $R$: a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} R$, a commutative relative group law $L$, the property bundle `AbelianSchemePropertyBundle`, all fibres of topological Krull dimension $g$, $2g$ sections $P_i$ killed by $n$ which freely generate the $n$-torsion of every geometric fibre, and an invertible module $\mathcal{L} = u.\mathrm{pol}$ admitting a closed immersion by sections and with geometric fibre $H^0$-rank $N+1$. Let $F$ be a Schrödinger frame of type $\delta$ for $\mathcal{L}$ along $\operatorname{Spec} R' \to \operatorname{Spec} R$: sections $\sigma_h$ of the pullback of $\mathcal{L}$ indexed by $h \in H(\delta)$ forming an $R'$-basis in the sense that $c \mapsto \sum_h \mathrm{baseScalar}(c_h)\cdot\sigma_h$ is bijective, together with theta points $\mathrm{lift}(h)$ and $\mathrm{dualLift}(\chi)$ acting on the $\sigma_h$ by translation $h' \mapsto h + h'$ and by the scalars $\chi(h)$ respectively. The conclusion is that there exists a framed polarised abelian scheme $X'$ over $R'$, that is, such data over $R'$ together with a `ProjPresentation` of its polarisation module in $\mathbb{P}^N_{R'}$ whose associated morphism is a closed immersion and whose $N+1$ sections form a section basis, such that: (i) the underlying polarised abelian scheme of $X'$ is a base change of $u$ along $R \to R'$, i.e. there is $g_A : X'.A \to A$ making a pullback square over $\operatorname{Spec} R' \to \operatorname{Spec} R$, compatible with the group laws and carrying the sections $P_i$ to those of $u$, and with $g_A^{*}\mathcal{L} \cong X'.\mathrm{pol}$; and (ii) $X'$ is theta-adapted for $\delta$ and $e$, i.e. some Schrödinger frame of type $\delta$ for $X'$ at the identity test morphism has its section indexed by $e(i)$ equal to the pullback local section of the $i$-th frame section of $X'$, for every $i$. The frame compatibility condition of `FramedPolarisedAbelianScheme.IsPullback` (agreement of the two morphisms to projective space) is not part of the assertion; only the polarised-abelian-scheme pullback is claimed.
--
--   This is the base-change step in the theory of theta structures and theta coordinates for polarised abelian schemes: a Schrödinger frame of type $\delta$ existing over the base change is converted into an actual framed object over $R'$ whose projective frame is given by theta coordinates. It is used in the proof that a polarised abelian scheme of suitable symmetric type is of theta type locally.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isPullback_isThetaAdapted_of_schrodingerFrame.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isPullback_isThetaAdapted_of_schrodingerFrame
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    (u : PolarisedAbelianScheme g (N + 1) n R)
    (F : Polarisation.SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap R R'))) δ) :
    ∃ X' : FramedPolarisedAbelianScheme g N n R',
      PolarisedAbelianScheme.IsPullback (algebraMap R R') u X'.toPolarisedAbelianScheme ∧ X'.IsThetaAdapted δ e := by sorry
