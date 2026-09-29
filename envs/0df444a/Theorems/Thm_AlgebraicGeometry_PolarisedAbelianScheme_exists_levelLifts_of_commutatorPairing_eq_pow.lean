-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_of_commutatorPairing_eq_pow
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_of_commutatorPairing_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/aaa5b86c-9072-5a26-a2d1-5868abf83577
-- title:
--   Étale-local Heisenberg level lifting of theta points
-- statement:
--   Fix natural numbers $g,d,n$ and $\delta:\mathrm{Fin}\,g\to\mathbb N$ with all $\delta_i$ and $d$ nonzero and $\prod_i\delta_i=d$, and write $H=\prod_i\mathbb Z/\delta_i$ and $K=H\times H$. Let $S$ be a commutative ring and $u$ a `PolarisedAbelianScheme g d n S`: an abelian scheme $f:A\to\operatorname{Spec} S$ with a commutative relative group law $L$, the property bundle of an abelian scheme, all fibres of topological Krull dimension $g$, together with $2g$ sections killed by $n$ that freely generate the $n$-torsion on every algebraically closed geometric fibre, and an invertible module `pol` on $A$ which is a closed immersion by sections over $f$ and has geometric fibre $H^0$-rank $d$. Let $R$ be an $S$-algebra in which $d$ is invertible, and $\zeta\in R^\times$ with $\zeta^d=1$ and $1-\zeta^j$ a unit for $0<j<d$. Write $t:\operatorname{Spec} R\to\operatorname{Spec} S$ for the structure morphism. Suppose given $x:K\to$ (morphisms $\operatorname{Spec} R\to A$ over $t$) which is additive, i.e. $x_0$ is the unit section and $x_{k+k'}=L.\mathrm{mul}\,x_k\,x_{k'}$; theta points $\theta^0_k$ over $t$ (each a point of $A$ together with an isomorphism between the pullback of `pol` along translation by that point and the pullback of `pol`) with underlying point $x_k$; and a function $B:K\times K\to\mathbb Z/d$ such that for all $k,k'$ and all global sections $s$ of the pullback of `pol` to $A\times_{\operatorname{Spec} S}\operatorname{Spec} R$, the actions satisfy $\theta^0_k\cdot(\theta^0_{k'}\cdot s)=\zeta^{\,(B(k,k'))^{\mathrm{val}}}\,\theta^0_{k'}\cdot(\theta^0_k\cdot s)$, the scalar acting through the base, and such that $B$ is additive in each variable, alternating ($B(a,a)=0$) and nondegenerate (if $B(a,b)=0$ for all $b$ then $a=0$). Then there exists a commutative ring $R'$, an $R$-algebra and $S$-algebra with the two structures forming a scalar tower over $S$, such that $R'$ is faithfully flat and étale over $R$, and there exist maps $\mathrm{lift}:H\to$ theta points over $\operatorname{Spec} R'$ and $\mathrm{dualLift}:\operatorname{Hom}(H,\mathbb Z/d)\to$ theta points over $\operatorname{Spec} R'$, both carrying $0$ to $1$ and sums to products, satisfying the Heisenberg commutation rule $\mathrm{dualLift}(c)\cdot\mathrm{lift}(h)=\mathrm{ofScalar}(\zeta_{R'}^{\,(c(h))^{\mathrm{val}}})\cdot(\mathrm{lift}(h)\cdot\mathrm{dualLift}(c))$ for all $c$ and $h$, where $\zeta_{R'}$ is the image of $\zeta$ in $R'^\times$ and $\mathrm{ofScalar}$ is the theta point given by multiplication by a unit of the base. The conclusion asserts only the existence of such a pair of homomorphisms into the theta group over $R'$; no compatibility with the given $x$ or $\theta^0$ is recorded.
--
--   This is the étale-local splitting of a theta group into two complementary level subgroups in the style of Mumford's theory of theta groups: a nondegenerate alternating commutator pairing with values in $\mu_d$ is put in symplectic normal form, and the two Lagrangian halves are lifted to homomorphic sections of the theta group over a faithfully flat étale cover, interacting by the Heisenberg rule. It feeds the construction of level structures in [`AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_of_rootedSymmetricOfType`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_of_rootedSymmetricOfType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_of_commutatorPairing_eq_pow.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_of_commutatorPairing_eq_pow
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] [NeZero d] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] [Algebra S R] (hdR : IsUnit ((d : ℕ) : R))
    (ζ : Rˣ) (hζ : (ζ : R) ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - (ζ : R) ^ j))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S R))) u.f)
    (hx0 : x 0 = u.L.one _) (hx : ∀ k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), x (k + k') = u.L.mul _ (x k) (x k'))
    (θ₀ : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S R)))) (hθ₀ : ∀ k, (θ₀ k).pt = x k)
    (B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d)
    (hB : ∀ (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))).obj u.pol, ⊤)),
      (θ₀ k).act ((θ₀ k').act s) = baseScalar u.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) ((ζ : R) ^ (B k k').val) • (θ₀ k').act ((θ₀ k).act s))
    (hadd₁ : ∀ a b c, B (a + b) c = B a c + B b c) (hadd₂ : ∀ a b c, B a (b + c) = B a b + B a c)
    (halt : ∀ a, B a a = 0) (hnd : ∀ a, (∀ b, B a b = 0) → a = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra S R') (_ : IsScalarTower S R R'),
      Module.FaithfullyFlat R R' ∧ Algebra.Etale R R' ∧
      ∃ (lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S R'))))
        (dualLift : (((i : Fin g) → ZMod (δ i)) →+ ZMod d) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S R')))),
        lift 0 = 1 ∧ (∀ h h' : ((i : Fin g) → ZMod (δ i)), lift (h + h') = lift h * lift h') ∧
        dualLift 0 = 1 ∧ (∀ c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, dualLift (c + c') = dualLift c * dualLift c') ∧
        (∀ (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d) (h : ((i : Fin g) → ZMod (δ i))),
          dualLift c * lift h =
            ThetaPt.ofScalar (Units.map (algebraMap R R' : R →* R') ζ ^ (c h).val) * (lift h * dualLift c)) := by sorry
