-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_forall_trace_eq_intCast_of_isFormalCoordinates_of_isSpecial
-- name    : CerednikDrinfeld.QM.forall_trace_eq_intCast_of_isFormalCoordinates_of_isSpecial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/2d0bb3f5-a384-5aa2-a028-a59992b37c64
-- title:
--   Drinfeld's trace condition for special formal mathcal O_D-modules
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a prime $r$, and a map $\mathrm{coord}:\Lambda\to \mathbb Z_{r^2}\times\mathbb Z_{r^2}$ (where $\mathbb Z_{r^2}$ is the Witt ring of $\mathbb F_{r^2}$) satisfying `IsOrderCoord`: it is additive and injective, sends $1$ (when $1\in\Lambda$) to $(1,0)$, is multiplicative for the twisted rule $(\alpha,\beta)(\alpha',\beta')=(\alpha\alpha'+r\beta\,\sigma(\beta'),\ \alpha\beta'+\beta\,\sigma(\alpha'))$ with $\sigma$ the Frobenius, has dense image modulo every power of $r$, and satisfies $\alpha_m+\sigma(\alpha_m)=n$ whenever $m+\bar m=n\in\mathbb Z$. Let $k$ be a field with a ring homomorphism $j:\mathbb Z_{r^2}\to k$, let $f:A\to\operatorname{Spec} k$ be a scheme over $k$ carrying a relative group law $L$ on its functor of points, and let $\mathrm{act}:\Lambda\to\operatorname{End}(A)$ assign to each $m$ an endomorphism over $k$ which, after push-forward on $T$-points, respects $L$'s multiplication for all $T$. Let $X$ be a formal $\mathcal O_D$-module of dimension $2$ over $k$ (a commutative two-variable formal group law $X.F$ with a $\mathbb Z_{r^2}$-action and a uniformiser $X.\varpi$ with $\varpi\circ\varpi=[r]$ and $\varpi\circ[\alpha]=[\sigma\alpha]\circ\varpi$), and let $\theta$ be formal coordinates for $f$ in $2$ variables with `L.IsFormalCoordinates X.F θ`: $\theta$ is natural in nilpotent argument tuples, and for every $k$-algebra $B'$ and ideal $J$ with $J^{n+1}=0$ it maps $J$-tuples bijectively onto the $J$-infinitesimal points of $f$, carrying the $n$-truncated group law of $X.F$ to $L$'s multiplication. Assume further that on such $J$-tuples the action of each $m\in\Lambda$ is computed by the series $X.\mathrm{act}(\alpha_m)+_{X.F}\bigl(X.\mathrm{act}(\beta_m)\circ X.\varpi\bigr)$, i.e. $\theta$ of the truncated evaluation of that series at $s$ equals the push-forward along $\mathrm{act}\,m$ of $\theta(s)$; and assume $X$ is special for $j$, meaning that the two subspaces $\mathrm{lieZero}\,j$ and $\mathrm{lieOne}\,j$ of the Lie algebra of $X$ (the eigenspaces where the $\mathbb Z_{r^2}$-action is $j$, respectively $j\circ\sigma$) are complementary and each invertible. The conclusion is Drinfeld's trace condition: for every algebraically closed field $k'$, every ring homomorphism $sk:k\to k'$, every finite-dimensional $k'$-vector space $V$ and every injective $\tau:V\to$ (points of $f$ over the dual-number base $\operatorname{Spec} k'[\varepsilon]\to\operatorname{Spec} k$ induced by $sk$) whose image is exactly the set of tangent vectors (those points restricting along $\operatorname{Spec} k'\to\operatorname{Spec} k'[\varepsilon]$ to the unit section at the geometric point), which is additive for $L$'s multiplication and compatible with scalars through the dual-number scaling maps, and for every $m\in\Lambda$ and $k'$-linear $\Phi:V\to V$ with $\tau(\Phi v)$ the push-forward of $\tau(v)$ along $\mathrm{act}\,m$, and every integer $n'$ with $m+\bar m=n'$ in $\mathbb H[\mathbb Q,a,b]$, one has $\operatorname{tr}_{k'}(\Phi)=n'$ in $k'$.
--
--   This is the trace (determinant) condition of Drinfeld's moduli problem for special formal $\mathcal O_D$-modules, in the form needed for the Čerednik–Drinfeld uniformisation: speciality of the formal module attached to a $\Lambda$-action forces the trace of the differential of $m$ on any tangent presentation to be the reduced trace of $m$. It supplies the trace conjunct required when a fake elliptic curve with its quaternionic action is reconstructed over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_forall_trace_eq_intCast_of_isFormalCoordinates_of_isSpecial.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.forall_trace_eq_intCast_of_isFormalCoordinates_of_isSpecial
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] (j : Zp2 r →+* k)
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (act : ↥Λ → (A ⟶ A)) (hact : ∀ x : ↥Λ, act x ≫ f = f)
    (hact_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (act x) (hact x) (L.mul t P Q) = L.mul t (pushPt (act x) (hact x) P) (pushPt (act x) (hact x) Q))

    (X : FormalODModule r k) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates X.F θ)
    (hθact : ∀ (B' : Type) [CommRing B'] [Algebra k B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ (m : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval n
            (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) i) s) =
          pushPt (act m) (hact m) (θ B' s))

    (hX : X.IsSpecial j) :
    ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k')
      (V : Type) [AddCommGroup V] [Module k' V] [Module.Finite k' V] (τ : V → SchemeHomOver (tangentBase k' sk) f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k' sk) f, P ∈ Set.range τ ↔ IsTangentVector L k' sk P) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k' sk) (τ v) (τ w)) →
      (∀ (c : k') (v : V), (τ (c • v)).1 = tangentScale k' c ≫ (τ v).1) →
      ∀ (m : ↥Λ) (Φ : V →ₗ[k'] V), (∀ v : V, τ (Φ v) = pushPt (act m) (hact m) (τ v)) →
      ∀ n' : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n' : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k' V Φ = (n' : k') := by sorry
