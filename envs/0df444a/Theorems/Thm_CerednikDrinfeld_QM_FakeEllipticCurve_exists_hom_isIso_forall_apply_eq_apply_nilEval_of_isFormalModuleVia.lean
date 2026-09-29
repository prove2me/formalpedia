-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_isIso_forall_apply_eq_apply_nilEval_of_isFormalModuleVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_isIso_forall_apply_eq_apply_nilEval_of_isFormalModuleVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/1debed14-9287-56c4-90b9-1db961095e3f
-- title:
--   Uniqueness of the formal 𝒪_D-module presentation of a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a prime $q$. Let $\mathrm{coord}\colon \Lambda \to \mathrm{Zp2}\,q \times \mathrm{Zp2}\,q$ (with $\mathrm{Zp2}\,q$ the Witt vectors of $\mathrm{GF}(q^2)$) satisfy `IsOrderCoord`: it is additive and injective, sends $1$ to $(1,0)$, is multiplicative for the twisted rule $(\alpha,\beta)(\alpha',\beta') = (\alpha\alpha' + q\,\beta\,\varphi(\beta'),\ \alpha\beta' + \beta\,\varphi(\alpha'))$ with $\varphi$ the Witt–vector Frobenius, has $q$-adically dense image, and satisfies $\alpha + \varphi(\alpha) = n$ whenever $m + m^{*} = n$. Let $B$ be a commutative ring in which $q$ is nilpotent, $E$ a fake elliptic curve over $B$ with $\Lambda$-action and level $N$ in the sense of `FakeEllipticCurve`, $X, X'$ formal $\mathcal{O}_D$-modules over $B$ (two-dimensional commutative formal group laws with a $\mathrm{Zp2}\,q$-action and a uniformiser series $\varpi$), and $\theta, \theta'$ formal coordinate systems of length $2$ for the structure morphism of $E$. Assume $\theta$ presents $X$ and $\theta'$ presents $X'$ as the formal module of $E$ through $\mathrm{coord}$, i.e. each $\theta$ is a formal coordinate system for the group law $E.L$ with associated formal group $X.F$ (resp. $X'.F$), and the action of each $m \in \Lambda$ on points is read off from $\mathrm{coord}\,m = (\alpha,\beta)$ as the series $X.\mathrm{act}(\alpha) +_{X.F} X.\mathrm{act}(\beta)\circ X.\varpi$. Then there is a morphism $u\colon X \to X'$ of formal $\mathcal{O}_D$-modules which is an isomorphism (admits a two-sided inverse morphism), such that for every $B$-algebra $B''$, every ideal $J$ of $B''$ with $J^{n+1} = 0$ and every $s\colon \mathrm{Fin}\,2 \to J$ one has $\theta\,s = \theta'\bigl(i \mapsto \mathrm{nilEval}\,n\,(u.\mathrm{toSeries}\,i)\,s\bigr)$, evaluation being truncation of the $i$-th component series in degrees $\le n$ in each variable; and $u$ is the unique morphism $X \to X'$ with this intertwining property.
--
--   This is the rigidity statement underlying the Serre–Tate style dictionary in the Čerednik–Drinfel'd setting: the formal $\mathcal{O}_D$-module attached to a fake elliptic curve together with its coordinatisation is determined up to a unique isomorphism. It is used in the construction of the Serre–Tate dictionary for deformations of fake elliptic curves, [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_serreTateDictionary_of_prorepresents_deformations`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_serreTateDictionary_of_prorepresents_deformations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_isIso_forall_apply_eq_apply_nilEval_of_isFormalModuleVia.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_isIso_forall_apply_eq_apply_nilEval_of_isFormalModuleVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B)
    (X X' : FormalODModule q B) (θ θ' : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hX : E.IsFormalModuleVia coord X θ) (hX' : E.IsFormalModuleVia coord X' θ') :
    ∃ u : FormalODModule.Hom X X', u.IsIso ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (u.toSeries i) s)) ∧
      ∀ u₂ : FormalODModule.Hom X X',
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (u₂.toSeries i) s)) → u₂ = u := by sorry
