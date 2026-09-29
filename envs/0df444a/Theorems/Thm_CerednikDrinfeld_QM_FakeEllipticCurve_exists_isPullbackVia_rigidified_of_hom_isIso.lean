-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_rigidified_of_hom_isIso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_rigidified_of_hom_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/118b9f49-4eea-55e2-9199-0853840d73a3
-- title:
--   Serre–Tate lifting with prescribed rigidified formal module
-- statement:
--   Fix rationals $a,b$, an additive subgroup $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a prime $q$, together with a map $\mathrm{coord} : \Lambda \to \mathbb{Z}_{q,2} \times \mathbb{Z}_{q,2}$ (values in the Witt vectors of $\mathbb{F}_{q^2}$) satisfying `IsOrderCoord`: it is additive and injective, sends $1$ to $(1,0)$, is compatible with multiplication in $\Lambda$ through the twisted rule $(\alpha_1\beta_1 + q\,\alpha_2\,\varphi(\beta_2),\ \alpha_1\beta_2 + \alpha_2\,\varphi(\beta_1))$ where $\varphi$ is the Witt-vector Frobenius, has $q$-adically dense image, and computes reduced traces via $\alpha_1 + \varphi(\alpha_1)$; assume also $1 \in \Lambda$. Let $B$ be an Artinian local ring with algebraically closed residue field, and $B_0$ a $B$-algebra whose structure map is surjective with nilpotent kernel; assume $q$ is nilpotent in $B$ and $N$ is a unit in $B$. Let $E_0$ be a fake elliptic curve over $B_0$ for $(\Lambda,N)$, $X_0$ a formal $\mathcal{O}_D$-module of dimension $2$ over $B_0$, and $\theta_0$ a system of formal coordinates for $E_0.f$ in two variables which exhibits $X_0$ as the formal module of $E_0$ through $\mathrm{coord}$. Let $X$ be a formal $\mathcal{O}_D$-module over $B$ and $w$ a homomorphism from the base change $X \otimes_B B_0$ to $X_0$ admitting a two-sided inverse. Then there exist a fake elliptic curve $E$ over $B$, a morphism $g : E_0.A \to E.A$, and formal coordinate systems $\theta$ for $E.f$ and $\tilde\theta$ for $E_0.f$ such that: $g$ makes $E_0$ the pullback of $E$ along $\operatorname{Spec} B_0 \to \operatorname{Spec} B$ in the sense of `IsPullbackVia` (a pullback square compatible with the group laws, with the $\Lambda$-actions, and with points factoring through the level structures); $\theta$ exhibits $X$ as the formal module of $E$ through $\mathrm{coord}$; $\tilde\theta$ exhibits $X \otimes_B B_0$ as the formal module of $E_0$ through $\mathrm{coord}$; for every $B''$ that is simultaneously a $B$- and $B_0$-algebra compatibly, and every pair $s$ of nilpotent elements of $B''$, the point $\tilde\theta(s)$ followed by $g$ is $\theta(s)$; and for every $B_0$-algebra $B''$, every ideal $J$ with $J^{n+1} = 0$ and every pair $s$ of elements of $J$, one has $\tilde\theta(s) = \theta_0\bigl(\mathrm{nilEval}_n(w_i)(s)\bigr)$, the truncated substitution of $s$ into the power series defining $w$.
--
--   This is the existence (surjectivity) half of the Serre–Tate dictionary in the Čerednik–Drinfeld setting: every formal $\mathcal{O}_D$-module over an Artinian local base, rigidified by an isomorphism of its reduction with the formal module of a given fake elliptic curve over $B_0$, arises from a deformation of that curve, with coordinates on both levels matched by the rigidification. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedCurve_lift_of_isArtinianRing`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedCurve_lift_of_isArtinianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_rigidified_of_hom_isIso.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_rigidified_of_hom_isIso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (IsLocalRing.ResidueField B)]
    [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hq : IsNilpotent ((q : ℕ) : B)) (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (X₀ : FormalODModule q B₀) (θ₀ : RelativeGroupLaw.FormalCoordinates E₀.f 2)
    (hX₀ : E₀.IsFormalModuleVia coord X₀ θ₀)
    (X : FormalODModule q B) (w : (X.map (algebraMap B B₀)).Hom X₀) (hwI : w.IsIso) :
    ∃ (E : FakeEllipticCurve Λ N B) (g : E₀.A ⟶ E.A) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
      (θt : RelativeGroupLaw.FormalCoordinates E₀.f 2),
      FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E E₀ g ∧
      E.IsFormalModuleVia coord X θ ∧
      E₀.IsFormalModuleVia coord (X.map (algebraMap B B₀)) θt ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''] [IsScalarTower B B₀ B''] (s : Fin 2 → B''),
        (∀ i, IsNilpotent (s i)) → (θt B'' s).1 ≫ g = (θ B'' s).1) ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra B₀ B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          θt B'' s = θ₀ B'' (fun i => MvFormalGroup.nilEval n (w.toSeries i) s)) := by sorry
