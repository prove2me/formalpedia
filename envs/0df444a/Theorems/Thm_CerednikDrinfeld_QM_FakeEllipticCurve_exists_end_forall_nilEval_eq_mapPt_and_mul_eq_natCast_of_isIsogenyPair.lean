-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_end_forall_nilEval_eq_mapPt_and_mul_eq_natCast_of_isIsogenyPair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_end_forall_nilEval_eq_mapPt_and_mul_eq_natCast_of_isIsogenyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/2bcd3162-5ec4-5643-952c-4bf56828e3ab
-- title:
--   Formal germ of a dual isogeny, arbitrary degree
-- statement:
--   Fix a prime $r$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a commutative ring $k_0$. Let $A_0$ be a fake elliptic curve over $k_0$ of type $(\Lambda,N)$ — a scheme $A_0.A$ with structure morphism $A_0.f$ to $\operatorname{Spec} k_0$, a commutative relative group law $A_0.L$ on its sections, the property bundle, two-dimensional fibres, and an action `A₀.act` of $\Lambda$ by endomorphisms over $k_0$ compatible with the group law. Let `coord` assign to each $m \in \Lambda$ a pair of elements of $W(\mathbb{F}_{r^2})$, let $X_0$ be a formal $\mathcal{O}_D$-module over $k_0$ (a commutative two-dimensional formal group $X_0.F$ with an action of $W(\mathbb{F}_{r^2})$ by series and a uniformiser series `varpi`), and let $\theta_0$ be a system of formal coordinates of dimension $2$ for $A_0.f$, assumed via `IsFormalModuleVia` to be formal coordinates for $A_0.L$ with formal group $X_0.F$ and to convert, on nilpotent points, the series $\mathrm{addVia}$ of $X_0.\mathrm{act}(\mathrm{coord}\,m)_1$ and $X_0.\mathrm{act}(\mathrm{coord}\,m)_2 \circ \mathrm{varpi}$ into the action of $m$ on $A_0$. Let $n$ be a natural number whose image in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $\Lambda$, and let $e,e' : A_0.A \to A_0.A$ be morphisms over $A_0.f$ (witnessed by `he`, `he'`) forming an isogeny pair of degree $n$: both are morphisms over the base, both respect the group law on points, both commute with the $\Lambda$-action, and $e \circ e'$ and $e' \circ e$ (in either composition order) are the action of $n \in \Lambda$. Suppose $\varepsilon$ is an endomorphism of $X_0.F$ inducing $e$ through $\theta_0$, in the sense that for every $k_0$-algebra $B'$, every ideal $J$ with $J^{m+1}=0$ and every $s : \mathrm{Fin}\,2 \to B'$ with all $s_i \in J$, the point $\theta_0\,B'$ evaluated at the truncated evaluations $\mathrm{nilEval}\,m(\varepsilon_i)(s)$ equals $\theta_0\,B'(s)$ followed by $e$. Then there exists an endomorphism $\varepsilon'$ of $X_0.F$ satisfying the same property with $e'$ in place of $e$, and such that for every endomorphism $\delta$ of $X_0.F$ which, in the same sense, induces the action of $n \in \Lambda$ on nilpotent points, one has $\varepsilon'\varepsilon = \delta$ and $\varepsilon\varepsilon' = \delta$.
--
--   This produces the formal germ of the dual member of an isogeny pair of arbitrary degree on a fake elliptic curve, together with the relation that the two germs compose in both orders to the germ of multiplication by the degree; it is the degree-agnostic form of the corresponding statement for $r$-power degrees. It is used in establishing the equivariance properties of the supersingular dictionary, where dual germs for isogenies of degree $\bar{r}r^k$ or $\ell r^k$ are needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_end_forall_nilEval_eq_mapPt_and_mul_eq_natCast_of_isIsogenyPair.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_end_forall_nilEval_eq_mapPt_and_mul_eq_natCast_of_isIsogenyPair
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k₀ : Type} [CommRing k₀]
    (A₀ : FakeEllipticCurve Λ N k₀) (coord : ↥Λ → Zp2 r × Zp2 r) (X₀ : FormalODModule r k₀)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (n : ℕ) (hn : (((n : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (e e' : A₀.A ⟶ A₀.A) (hee' : FakeEllipticCurve.IsIsogenyPair n A₀ A₀ e e')
    (he : e ≫ A₀.f = A₀.f) (he' : e' ≫ A₀.f = A₀.f)
    (ε : MvFormalGroup.End X₀.F)
    (hε : ∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m (ε.toPowerSeries i) s) = mapPt e he (θ₀ B' s)) :
    ∃ ε' : MvFormalGroup.End X₀.F,
      (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt e' he' (θ₀ B' s)) ∧
      ∀ δ : MvFormalGroup.End X₀.F,
        (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
          ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
            θ₀ B' (fun i => MvFormalGroup.nilEval m (δ.toPowerSeries i) s) =
              mapPt (A₀.act ⟨((n : ℕ) : ℚ), hn⟩) (A₀.act_over _) (θ₀ B' s)) →
        ε' * ε = δ ∧ ε * ε' = δ := by sorry
