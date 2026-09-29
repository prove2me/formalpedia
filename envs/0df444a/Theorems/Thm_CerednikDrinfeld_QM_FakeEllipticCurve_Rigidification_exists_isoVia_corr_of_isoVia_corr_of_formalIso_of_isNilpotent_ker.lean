-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isoVia_corr_of_formalIso_of_isNilpotent_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_of_isoVia_corr_of_formalIso_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/206027d2-70c5-5837-a56c-2e739c5bbf56
-- title:
--   Lifting a rigidified isomorphism along a nilpotent thickening
-- statement:
--   Fix a prime $r$, a natural number $N$, a commutative ring $\mathcal{O}$ with an element $\pi$, an $\mathcal{O}$-algebra $O^{\mathrm{nr}}$, rationals $a,b$, and a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ containing every rational integer, together with a map $\mathrm{coord}:\Lambda\to \mathbb{Z}_{r^2}\times\mathbb{Z}_{r^2}$ satisfying `IsOrderCoord` (additive, sending $1$ to $(1,0)$, multiplicative for the Frobenius-twisted product, injective, with dense image modulo all powers of $r$, and computing reduced traces), and a fake elliptic curve $A_0$ of level $N$ over $O^{\mathrm{nr}}/(\pi)$. Let $p:B\to B_0$ be a surjective $\mathcal{O}$-algebra map with nilpotent kernel, $B$ Noetherian, $r$ nilpotent in $B$ and $N$ a unit in $B$, and let $\psi:O^{\mathrm{nr}}\to B$ be an $\mathcal{O}$-algebra map. Let $x=(E,\varrho)$ and $x'=(E',\varrho')$ be rigidified fake elliptic curves over $(B,\psi)$, each rigidification consisting of reductions $E_b$, $A_b$ over $B/(\pi)$ with comparison maps $g_b$, $g_A$ exhibiting $E_b$ as the reduction of $E$ and $A_b$ as the pullback of $A_0$, an exponent $d$, and a degree-$r^d$, level-preserving isogeny pair $\varphi,\varphi'$ between them. Let $X,X'$ be formal $\mathcal{O}_D$-modules over $B$ of dimension $2$ (commutative formal groups with $\mathbb{Z}_{r^2}$-action and uniformiser series $\varpi$ with $\varpi\circ\varpi=[r]$ and $\varpi\circ a=\sigma(a)\circ\varpi$), exhibited on $E$ and $E'$ by systems of formal coordinates $\theta,\theta'$ in two variables, in the sense that $\theta$ parametrises the infinitesimal points of the relative group law compatibly with $X.F$ and that the $\Lambda$-action is computed through $\mathrm{coord}$, and likewise for $\theta'$. Let $x_0,x_0'$ be rigidified fake elliptic curves over $(B_0,p\circ\psi)$, with morphisms $g,g'$ exhibiting the curves of $x,x'$ as pullbacks along $p$ (compatibly with group law, $\Lambda$-action and level) and with the rigidifications of $x_0,x_0'$ pulled back from those of $x,x'$. Assume given, downstairs, an isomorphism $e_0$ of the curves of $x_0$ and $x_0'$ over $B_0$ respecting group law, $\Lambda$-action and level, a map $i_{b,0}$ on the reductions compatible with $e_0$ through the $g_b$ and over $B/(\pi)$, a map $u_{A,0}$ of the $A_b$-parts which is a pullback along the identity and compatible with the $g_A$, and exponents $i_0,j_0$ with $i_{b,0}\circ\varphi_0'\circ u_{A,0}\circ[r^{i_0}]=\varphi_0\circ[r^{j_0}]$ (written in diagrammatic order). Assume further given an isomorphism $T:X\to X'$ of formal $\mathcal{O}_D$-modules such that, for every ring $B''$ which is simultaneously a $B$-algebra and a $B_0$-algebra with the structure maps compatible through $p$, every ideal $J$ of $B''$ with $J^{n+1}=0$, every $s:\mathrm{Fin}\,2\to J$ and every point $p_0$ of $x_0$ over $\mathrm{Spec}\,B''$ with $p_0$ followed by $g$ equal to $\theta(B'')(s)$, the point $p_0$ followed by $e_0$ and then $g'$ equals $\theta'(B'')$ evaluated at the truncations of the series of $T$ at $s$. Then there exist an isomorphism $i$ of the curve of $x$ with that of $x'$ over $B$, respecting group law, $\Lambda$-action and level, with $g$ followed by $i$ equal to $e_0$ followed by $g'$, a map $i_b$ of the reductions compatible with $i$ through the $g_b$ and over $B/(\pi)$, a map $u_A$ of the $A_b$-parts which is a pullback along the identity and compatible with the $g_A$, and exponents $i_1,j_1$ with $i_b\circ\varphi'\circ u_A\circ[r^{i_1}]=\varphi\circ[r^{j_1}]$.
--
--   This is the Serre–Tate style rigidity statement for the moduli of rigidified fake elliptic curves: an isomorphism of rigidified objects over $B_0$ together with an isomorphism of the associated formal $\mathcal{O}_D$-modules over $B$ inducing it on infinitesimal points lifts to an isomorphism over $B$, with matching rigidification data up to $r$-power multiplication. It is the thickening step used in the proof of injectivity in `rigidifiedToG_surjective_injective_of_isArtinianRing_of_isAlgClosed_residueField`, where one takes $B_0$ to be the residue field of an Artinian local base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isoVia_corr_of_formalIso_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_of_isoVia_corr_of_formalIso_of_isNilpotent_ker
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] [CommRing B₀] [Algebra 𝒪 B₀]
    (p : B →ₐ[𝒪] B₀) (hp : Function.Surjective p) (hker : IsNilpotent (RingHom.ker (p : B →+* B₀)))
    (hBr : IsNilpotent ((r : ℕ) : B)) (hNB : IsUnit ((N : ℕ) : B))
    (ψ : Onr →ₐ[𝒪] B)

    (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ)
    (X X' : FormalODModule r B)
    (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2)
    (hX : x.1.IsFormalModuleVia coord X θ) (hX' : x'.1.IsFormalModuleVia coord X' θ')

    (x₀ x₀' : FakeEllipticCurve.RigidifiedCurve r π A₀ B₀ (p.comp ψ))
    (g : x₀.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) x.1 x₀.1 g)
    (hρ : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg x.2 x₀.2)
    (g' : x₀'.1.A ⟶ x'.1.A) (hg' : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) x'.1 x₀'.1 g')
    (hρ' : FakeEllipticCurve.Rigidification.IsPullbackVia p g' hg' x'.2 x₀'.2)

    (e₀ : x₀.1.A ≅ x₀'.1.A) (he₀ : e₀.hom ≫ x₀'.1.f = x₀.1.f) (he₀V : FakeEllipticCurve.IsoVia x₀.1 x₀'.1 e₀ he₀)
    (ib₀ : x₀.2.Eb.A ⟶ x₀'.2.Eb.A) (hib₀ : ib₀ ≫ x₀'.2.gb = x₀.2.gb ≫ e₀.hom) (hib₀f : ib₀ ≫ x₀'.2.Eb.f = x₀.2.Eb.f)
    (uA₀ : x₀'.2.Ab.A ⟶ x₀.2.Ab.A) (huA₀ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x₀.2.Ab x₀'.2.Ab uA₀)
    (huA₀g : uA₀ ≫ x₀.2.gA = x₀'.2.gA) (i₀ j₀ : ℕ)
    (hcorr₀ : ib₀ ≫ x₀'.2.φ ≫ uA₀ ≫ x₀.2.Ab.act ⟨(((r ^ i₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      x₀.2.φ ≫ x₀.2.Ab.act ⟨(((r ^ j₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (T : FormalODModule.Hom X X') (hT : T.IsIso)
    (hTe₀ : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''],
      algebraMap B B'' = (algebraMap B₀ B'').comp (p : B →+* B₀) →
      ∀ (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ → ∀ (s : Fin 2 → B''), (∀ i, s i ∈ J) →
      ∀ p₀ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) B'') x₀.1.f, p₀.1 ≫ g = (θ B'' s).1 →
        p₀.1 ≫ e₀.hom ≫ g' = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toSeries i) s)).1) :
    ∃ (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f),
      FakeEllipticCurve.IsoVia x.1 x'.1 i hi ∧ g ≫ i.hom = e₀.hom ≫ g' ∧
      ∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
        (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA)
        (_ : uA ≫ x.2.gA = x'.2.gA) (i₁ j₁ : ℕ),
        ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
          x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
