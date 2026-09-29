-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isODHom_forall_comp_eq_apply_nilEval_of_isFormalModuleVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isODHom_forall_comp_eq_apply_nilEval_of_isFormalModuleVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/52969864-602f-5ea9-a2e5-715884a16d6e
-- title:
--   Formal germ of a Λ-linear map is an 𝒪_D-homomorphism
-- statement:
--   Fix a prime $r$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a map $\mathrm{coord}\colon\Lambda\to\mathrm{Zp2}(r)\times\mathrm{Zp2}(r)$ into two copies of the Witt vectors of $\mathbb{F}_{r^2}$ which is an order coordinate in the sense of `IsOrderCoord`: it is additive, sends $1$ (when $1\in\Lambda$) to $(1,0)$, satisfies the twisted multiplication rule $\mathrm{coord}(mm')=(\alpha\alpha'+r\beta\,\varphi(\beta'),\ \alpha\beta'+\beta\,\varphi(\alpha'))$ for $\mathrm{coord}(m)=(\alpha,\beta)$, $\mathrm{coord}(m')=(\alpha',\beta')$ and $\varphi$ the Witt-vector Frobenius, is injective, has $r$-adically dense image in each coordinate, and satisfies $\alpha+\varphi(\alpha)=n$ whenever $m+\bar m=n\in\mathbb{Z}$. Let $L$ be a Noetherian commutative ring in which the image of $r$ is nilpotent, and let $E,E'$ be fake elliptic curves over $L$ for $(\Lambda,N)$, i.e. schemes $E.A\to\operatorname{Spec}L$ carrying a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action by endomorphisms over $L$ compatible with the group law and the trace condition, and the auxiliary level data. Let $q\colon E.A\to E'.A$ satisfy $q$ followed by $E'.f$ equals $E.f$, let $q$ carry the group law of $E$ to that of $E'$ on points over any base (pushing forward points by post-composition with $q$), and let $q$ intertwine the two $\Lambda$-actions, $E.\mathrm{act}(x)$ followed by $q$ equalling $q$ followed by $E'.\mathrm{act}(x)$ for all $x\in\Lambda$. Finally let $X,X'$ be formal $\mathcal{O}_D$-modules of dimension $2$ over $L$ at $r$ (a commutative two-variable formal group law with a $\mathrm{Zp2}(r)$-action and a uniformiser series $\Pi$ with $\Pi\circ\Pi=[r]$ and $\Pi\circ[\alpha]=[\varphi(\alpha)]\circ\Pi$), and $\theta,\theta'$ formal coordinates of dimension $2$ along the unit sections of $E.f$, $E'.f$ exhibiting $X$, $X'$ via $\mathrm{coord}$, in the sense that $\theta$ is a system of formal coordinates for the group law with law $X.F$ and that each $m\in\Lambda$ acts on nilpotent points through the series $[\alpha_m]+_{X.F}[\beta_m]\circ\Pi$, and likewise for $\theta'$. Then there exists $\hat q$, a pair of formal power series in two variables over $L$, which is an $\mathcal{O}_D$-homomorphism $X\to X'$ (a homomorphism $X.F\to X'.F$ of laws commuting with every $[\alpha]$, $\alpha\in\mathrm{Zp2}(r)$, and with the uniformisers), and which represents $q$ on nilpotent points: for every $L$-algebra $B''$, every ideal $J$ with $J^{n+1}=0$ and every $s\colon\mathrm{Fin}\,2\to B''$ with all $s_i\in J$, the underlying scheme morphism of $\theta_{B''}(s)$ followed by $q$ equals the underlying morphism of $\theta'_{B''}$ evaluated at the vector obtained from $\hat q$ by truncating each component in degree $\le n$ in each variable and substituting $s$.
--
--   This is the passage from a $\Lambda$-linear homomorphism of fake elliptic curves over an $r$-nilpotent base to its formal germ along the unit sections, expressed in the formal coordinates that identify those germs with formal $\mathcal{O}_D$-modules in the sense of Drinfeld. It feeds the rigidification step of the Čerednik–Drinfeld uniformisation, where series representing morphisms are compared with powers of the $\mathcal{O}_D$-action and with Atkin–Lehner and Frobenius data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isODHom_forall_comp_eq_apply_nilEval_of_isFormalModuleVia.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isODHom_forall_comp_eq_apply_nilEval_of_isFormalModuleVia
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    {L : Type} [CommRing L] [IsNoetherianRing L] (hLr : IsNilpotent ((r : ℕ) : L))
    (E E' : FakeEllipticCurve Λ N L) (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t E.f),
      mapPt q hq (E.L.mul t P Q) = E'.L.mul t (mapPt q hq P) (mapPt q hq Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ q = q ≫ E'.act x)
    (X : FormalODModule r L) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (X' : FormalODModule r L) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hX' : E'.IsFormalModuleVia coord X' θ') :
    ∃ qhat : Series L, FormalODModule.IsODHom X X' qhat ∧
      ∀ (B'' : Type) [CommRing B''] [Algebra L B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ q = (θ' B'' (fun i => MvFormalGroup.nilEval n (qhat i) s)).1 := by sorry
