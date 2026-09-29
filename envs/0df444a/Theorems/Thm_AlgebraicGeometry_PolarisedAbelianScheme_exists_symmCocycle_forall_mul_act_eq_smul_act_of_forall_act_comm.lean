-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_symmCocycle_forall_mul_act_eq_smul_act_of_forall_act_comm
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_symmCocycle_forall_mul_act_eq_smul_act_of_forall_act_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/70ae3b18-b436-58a1-a7dd-10bb65ef3476
-- title:
--   A symmetric 2-cocycle from commuting theta points
-- statement:
--   Let $u$ be a polarised abelian scheme of the project's kind over a commutative ring $S$ with parameters $g,d,n$: an $S$-scheme $u.f : A \to \operatorname{Spec} S$ carrying a commutative relative group law $u.L$, the abelian-scheme property bundle, fibres of topological Krull dimension $g$, $2g$ $n$-torsion sections that are independent and span the $n$-torsion on algebraically closed fibres, and an invertible module $u.pol$ that is a closed immersion by sections with geometric fibre $H^0$-rank $d$. Let $t : \operatorname{Spec} R \to \operatorname{Spec} S$ be a morphism for a commutative ring $R$, and let $K_1$ be a finite additive abelian group. Given a family $x : K_1 \to \{\varphi : \operatorname{Spec} R \to A \mid \varphi \text{ followed by } u.f = t\}$ with $x(0)$ the unit section and $x(k+k') = u.L.\mathrm{mul}\,t\,(x\,k)\,(x\,k')$, and theta points $\theta^0_k$ for $u.f, u.L, u.pol$ over $t$ (each a point together with an isomorphism between the translate by that point of the pullback of $u.pol$ to $A\times_S\operatorname{Spec} R$ and that pullback) whose underlying points satisfy $(\theta^0_k).\mathrm{pt} = x\,k$, and such that the induced operators on $\Gamma$ of the pulled-back $u.pol$ pairwise commute, the conclusion asserts the existence of $c : K_1 \to K_1 \to R^\times$ such that, for all $k,k'$ and all global sections $s$, $(\theta^0_k\theta^0_{k'}).\mathrm{act}\,s = \mathrm{baseScalar}(c\,k\,k')\cdot (\theta^0_{k+k'}).\mathrm{act}\,s$, together with $c\,k\,k' = c\,k'\,k$ and $c\,a\,b \cdot c\,(a+b)\,k = c\,b\,k \cdot c\,a\,(b+k)$. The proof uses neither the normalisation $x(0) = 1$ nor the finiteness of $K_1$.
--
--   This is the first step of the Lagrangian-splitting construction in Mumford's theory of theta groups: a family of theta points lying over a subgroup of points, with pairwise commuting actions, differs from a homomorphic family by a symmetric $2$-cocycle with values in the units of the base. It is used in the construction of a faithfully flat étale level lift for such a commuting family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_symmCocycle_forall_mul_act_eq_smul_act_of_forall_act_comm.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_symmCocycle_forall_mul_act_eq_smul_act_of_forall_act_comm
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {K₁ : Type} [AddCommGroup K₁] [Fintype K₁]
    (x : K₁ → SchemeHomOver t u.f) (hx0 : x 0 = u.L.one t) (hx : ∀ k k' : K₁, x (k + k') = u.L.mul t (x k) (x k'))
    (θ₀ : K₁ → ThetaPt u.f u.L u.pol t) (hθ₀ : ∀ k : K₁, (θ₀ k).pt = x k)
    (hcomm : ∀ (k k' : K₁) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)), (θ₀ k).act ((θ₀ k').act s) = (θ₀ k').act ((θ₀ k).act s)) :
    ∃ c : K₁ → K₁ → Rˣ,
      (∀ (k k' : K₁) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)), (θ₀ k * θ₀ k').act s = baseScalar u.f t ((c k k' : Rˣ) : R) • (θ₀ (k + k')).act s) ∧
      (∀ k k' : K₁, c k k' = c k' k) ∧
      (∀ a b k : K₁, c a b * c (a + b) k = c b k * c a (b + k)) := by sorry
