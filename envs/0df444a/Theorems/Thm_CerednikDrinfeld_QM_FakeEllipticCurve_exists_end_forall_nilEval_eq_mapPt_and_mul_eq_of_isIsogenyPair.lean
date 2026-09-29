-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_end_forall_nilEval_eq_mapPt_and_mul_eq_of_isIsogenyPair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_end_forall_nilEval_eq_mapPt_and_mul_eq_of_isIsogenyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/86a2f0c8-83f2-58a7-bdc0-6b0067383082
-- title:
--   Formal germ of the dual isogeny on a fake elliptic curve
-- statement:
--   Fix a prime $r$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a commutative ring $k_0$. Let $A_0$ be a fake elliptic curve of type $(\Lambda,N)$ over $k_0$, with structure morphism $A_0.f$ and relative group law $A_0.L$, let $\mathrm{coord}:\Lambda\to \mathbb{Z}_{r^2}\times\mathbb{Z}_{r^2}$, let $X_0$ be a formal $\mathcal{O}_D$-module of height data $r$ over $k_0$ (a two-dimensional commutative formal group $X_0.F$ with $\mathbb{Z}_{r^2}$-action and uniformiser series), and let $\theta_0$ be a system of formal coordinates in $2$ parameters for $A_0.f$ satisfying `IsFormalModuleVia coord X₀ θ₀`; of this hypothesis the proof uses only its first clause, that $\theta_0$ is a system of formal coordinates for $A_0.L$ with formal group $X_0.F$ (functoriality in $k_0$-algebras, and for each ideal $J$ with $J^{m+1}=0$ a bijection between tuples in $J$ and $J$-infinitesimal points, compatible with truncated multiplication). Let $d$ be a natural number with $r^d\in\Lambda$ (as a rational scalar, via `hd`), and let $e,e':A_0.A\to A_0.A$ be an isogeny pair of degree $r^d$ in the sense of `IsIsogenyPair`: each lies over $A_0.f$, each is additive for $A_0.L$ on all $T$-points, each commutes with the $\Lambda$-action, and the two composites equal the action of $r^d$; additionally $e$ and $e'$ are assumed to lie over $A_0.f$ by the explicit witnesses `he`, `he'`. Finally let $\varepsilon$ be an endomorphism of the formal group $X_0.F$ which is a formal germ of $e$: for every commutative $k_0$-algebra $B'$, every ideal $J\subseteq B'$ with $J^{m+1}=0$ and every $s:\mathrm{Fin}\,2\to J$, applying $\theta_0$ to the truncated evaluations `nilEval m` of the component series of $\varepsilon$ at $s$ gives the point $\theta_0(s)$ followed by $e$. The conclusion asserts the existence of an endomorphism $\varepsilon'$ of $X_0.F$ which is a formal germ of $e'$ in the same sense, and such that for every endomorphism $\delta$ of $X_0.F$ that is a formal germ of the action of $r^d$ on $A_0$ one has $\varepsilon'\varepsilon=\delta$ and $\varepsilon\varepsilon'=\delta$.
--
--   This is the passage from an isogeny pair of degree $r^d$ on a fake elliptic curve to the corresponding pair of endomorphisms of its two-dimensional formal $\mathcal{O}_D$-module, recording that the germ of the dual isogeny exists and that the two composites of germs coincide with any germ of multiplication by $r^d$. It feeds the construction of duals and kernels of level isogenies in the Cerednik–Drinfeld setting, and the identification of the endomorphism action on the rigidified formal module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_end_forall_nilEval_eq_mapPt_and_mul_eq_of_isIsogenyPair.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_end_forall_nilEval_eq_mapPt_and_mul_eq_of_isIsogenyPair
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k₀ : Type} [CommRing k₀]
    (A₀ : FakeEllipticCurve Λ N k₀) (coord : ↥Λ → Zp2 r × Zp2 r) (X₀ : FormalODModule r k₀)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (d : ℕ) (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (e e' : A₀.A ⟶ A₀.A) (hee' : FakeEllipticCurve.IsIsogenyPair (r ^ d) A₀ A₀ e e')
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
              mapPt (A₀.act ⟨((r ^ d : ℕ) : ℚ), hd⟩) (A₀.act_over _) (θ₀ B' s)) →
        ε' * ε = δ ∧ ε * ε' = δ := by sorry
