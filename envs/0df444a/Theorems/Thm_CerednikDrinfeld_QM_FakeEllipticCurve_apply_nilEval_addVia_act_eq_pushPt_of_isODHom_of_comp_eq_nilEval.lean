-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_addVia_act_eq_pushPt_of_isODHom_of_comp_eq_nilEval
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_addVia_act_eq_pushPt_of_isODHom_of_comp_eq_nilEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/48feb22b-e21f-5c6e-a0c6-51dea28d4730
-- title:
--   Transport of the Λ-action along an 𝒪_D-linear formal quotient
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a prime $r$, and a map $\mathrm{coord}:\Lambda\to\mathbb{W}(\mathbb{F}_{r^2})^2$ satisfying `IsOrderCoord`: it is additive, sends $1$ (when $1\in\Lambda$) to $(1,0)$, is multiplicative for the twisted rule $(\alpha,\beta)(\alpha',\beta')=(\alpha\alpha'+r\beta\,\varphi(\beta'),\ \alpha\beta'+\beta\,\varphi(\alpha'))$ with $\varphi$ the Witt-vector Frobenius, is injective, has dense image in both coordinates, and satisfies $\alpha+\varphi(\alpha)=n$ whenever $m+\bar m=n$. Let $k$ be a field, $A$ a `FakeEllipticCurve` for $(\Lambda,N)$ over $k$, with scheme $A.A$, structure map $A.f$, commutative relative group law $A.L$ and $\Lambda$-action $A.\mathrm{act}$ over $\operatorname{Spec}k$. Let $X_A$ be a formal $\mathcal{O}_D$-module of height data $r$ over $k$ (a $2$-dimensional commutative formal group law with a $\mathbb{W}(\mathbb{F}_{r^2})$-action by series and a series $\varpi$ with $\varpi\circ\varpi=\mathrm{act}(r)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\varphi a)\circ\varpi$), and $\theta_A$ formal coordinates of dimension $2$ for $A.f$ with `IsFormalModuleVia coord`: $\theta_A$ are formal coordinates for $A.L$ with law $X_A.F$, and on every nilpotent test datum each $m\in\Lambda$ acts through the series $\mathrm{addVia}\,X_A.F\,(X_A.\mathrm{act}(\mathrm{coord}\,m)_1)\,((X_A.\mathrm{act}(\mathrm{coord}\,m)_2)\circ X_A.\varpi)$. Let $Y$ be a further formal $\mathcal{O}_D$-module, $\gamma$ a homomorphism of formal group laws $X_A.F\to Y.F$ commuting with the $\mathbb{W}(\mathbb{F}_{r^2})$-actions and with $\varpi$, whose kernel algebra $\mathrm{MvPowerSeries}(\mathrm{Fin}\,2,k)/(\gamma)$ is finite projective over $k$ of constant fibre rank $d$. Let $A'$ be a scheme with structure map $f'$ to $\operatorname{Spec}k$, $L'$ a relative group law on $f'$, and $\mathrm{act}':\Lambda\to\operatorname{End}(A')$ a family of endomorphisms over $f'$ each of which pushes forward $L'$-multiplication to $L'$-multiplication. Let $p:A.A\to A'$ satisfy $p$ followed by $f'$ equals $A.f$ and $A.\mathrm{act}(x)$ followed by $p$ equals $p$ followed by $\mathrm{act}'(x)$ for all $x\in\Lambda$. Let $\theta'$ be formal coordinates of dimension $2$ for $f'$, formal coordinates for $L'$ with law $Y.F$, and assume that on every nilpotent datum the germ of $p$ is $\gamma$: for each $k$-algebra $B''$, ideal $J$ with $J^{m+1}=0$ and $s$ with entries in $J$, the point $\theta_A(B'',s)$ followed by $p$ equals $\theta'(B'',(\mathrm{nilEval}_m(\gamma_i)(s))_i)$. Then for every $k$-algebra $B'$, ideal $J$ and $m$ with $J^{m+1}=0$, every $x\in\Lambda$ and every $s:\mathrm{Fin}\,2\to B'$ with entries in $J$, one has $\theta'(B',(\mathrm{nilEval}_m(\mathrm{addVia}\,Y.F\,(Y.\mathrm{act}(\mathrm{coord}\,x)_1)\,((Y.\mathrm{act}(\mathrm{coord}\,x)_2)\circ Y.\varpi)_i)(s))_i)$ equal to $\theta'(B',s)$ followed by $\mathrm{act}'(x)$.
--
--   This is the transport of the quaternionic action along an $\mathcal{O}_D$-linear isogeny of formal modules: the $\Lambda$-action on the target $A'$ is computed, in the formal coordinates $\theta'$, by the same recipe on $Y$ that describes it on $A$ via $X_A$, so that $\theta'$ exhibits $A'$ as a formal $\mathcal{O}_D$-module for $\Lambda$ with coordinate map $\mathrm{coord}$. It feeds the construction of quotients of fake elliptic curves by finite subgroup schemes cut out by $\gamma$, used in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_addVia_act_eq_pushPt_of_isODHom_of_comp_eq_nilEval.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_addVia_act_eq_pushPt_of_isODHom_of_comp_eq_nilEval
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k]

    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA)

    (Y : FormalODModule r k) (γ : Series k) (hγ : FormalODModule.IsODHom XA Y γ)
    {d : ℕ} (hγker : FormalODModule.HasKernelOfDegree γ d)

    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of k)} (L' : RelativeGroupLaw k f') (act' : ↥Λ → (A' ⟶ A'))
    (hact' : ∀ x : ↥Λ, act' x ≫ f' = f')
    (hact'_mul : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f'),
      pushPt (act' x) (hact' x) (L'.mul t P Q) = L'.mul t (pushPt (act' x) (hact' x) P) (pushPt (act' x) (hact' x) Q))
    (p : A.A ⟶ A') (hp : p ≫ f' = A.f) (hp_act : ∀ x : ↥Λ, A.act x ≫ p = p ≫ act' x)

    (θ' : RelativeGroupLaw.FormalCoordinates f' 2) (hθ' : L'.IsFormalCoordinates Y.F θ')
    (hgerm : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θA B'' s).1 ≫ p = (θ' B'' (fun i => MvFormalGroup.nilEval m (γ i) s)).1) :
    ∀ (B' : Type) [CommRing B'] [Algebra k B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ (x : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
        θ' B' (fun i => MvFormalGroup.nilEval m
            (Series.addVia Y.F (Y.act (coord x).1) ((Y.act (coord x).2).comp Y.varpi) i) s) =
          pushPt (act' x) (hact' x) (θ' B' s) := by sorry
