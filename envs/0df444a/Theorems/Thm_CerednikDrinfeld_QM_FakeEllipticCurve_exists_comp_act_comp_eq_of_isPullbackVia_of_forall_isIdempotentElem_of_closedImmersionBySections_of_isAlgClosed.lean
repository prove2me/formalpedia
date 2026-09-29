-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_act_comp_eq_of_isPullbackVia_of_forall_isIdempotentElem_of_closedImmersionBySections_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_act_comp_eq_of_isPullbackVia_of_forall_isIdempotentElem_of_closedImmersionBySections_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/82e25eeb-2a49-529d-b1bf-0dde2545c86d
-- title:
--   Descent of the exhaustion clause to idempotent-free bases
-- statement:
--   Fix natural numbers $r, N$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ containing the image of every rational integer, an algebraically closed field $k_0$ and a fake elliptic curve $A_0$ of type $(\Lambda, N)$ over $k_0$ (a scheme $A_0.A$ with a structure morphism $A_0.f$ to $\operatorname{Spec} k_0$, a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ by endomorphisms over the base satisfying the additivity, multiplicativity and trace conditions, and a level datum $A_0.\mathrm{lev}$). Assume given a module $\mathcal{L}$ on $A_0.A$ that is invertible (locally isomorphic to the unit sheaf) and satisfies `ClosedImmersionBySections` for $A_0.f$, i.e. admits a projective presentation by finitely many global sections whose associated morphism to projective space over $k_0$ is a closed immersion. Fix further rationals $a_1,b_1$, a subgroup $\tilde\Gamma \le (\mathbb{H}[\mathbb{Q},a_1,b_1])^{\times}$, maps $e, e' : \tilde\Gamma \to \operatorname{End}(A_0.A)$ with $e\gamma$ a morphism over $k_0$, and a function $\deg : \tilde\Gamma \to \mathbb{N}$, such that for each $\gamma$ the pair $(e\gamma, e'\gamma)$ is an isogeny pair of degree $r^{\deg\gamma}$ on $A_0$ (both morphisms lie over the base, are homomorphisms for the relative group law on all test points, commute with the $\Lambda$-action, and compose in either order to multiplication by $r^{\deg\gamma}$) and $e\gamma$ preserves the level, i.e. sends points factoring through $A_0.\mathrm{lev}$ to such points. Assume the exhaustion clause over $k_0$: every pair $(\varphi,\psi)$ of endomorphisms of $A_0.A$ forming an isogeny pair of degree $r^d$ with $\varphi$ over the base and level-preserving satisfies $\varphi$ followed by multiplication by $r^i$ equal to $e\gamma$ followed by multiplication by $r^j$, for some $\gamma \in \tilde\Gamma$ and $i,j \in \mathbb{N}$. The conclusion asserts: for every commutative ring $B$, every ring homomorphism $\psi_b : k_0 \to B$, every fake elliptic curve $A_b$ of type $(\Lambda,N)$ over $B$ and every morphism $g_A : A_b.A \to A_0.A$ exhibiting $A_b$ as the pullback of $A_0$ along $\psi_b$ in the sense of `IsPullbackVia` (the square with $A_b.f$, $A_0.f$ and $\operatorname{Spec}(\psi_b)$ is a pullback, $g_A$ is compatible with the two group laws and with the $\Lambda$-actions, and every level point of $A_b$ maps to a point factoring through $A_0.\mathrm{lev}$), and all $\varphi, \psi : A_b.A \to A_b.A$ and $d \in \mathbb{N}$ with $\varphi$ over the base, $(\varphi,\psi)$ an isogeny pair of degree $r^d$ on $A_b$ and $\varphi$ level-preserving, if every idempotent of $B$ equals $0$ or $1$ then there are $\gamma \in \tilde\Gamma$ and $i,j \in \mathbb{N}$ with $\varphi$ followed by multiplication by $r^i$ on $A_b$ followed by $g_A$ equal to $g_A$ followed by $e\gamma$ followed by multiplication by $r^j$ on $A_0$.
--
--   This is the base-change rigidity step for the exhaustion clause of the endomorphism dictionary attached to fake elliptic curves: knowing that every level-preserving isogeny pair of $r$-power degree over the algebraically closed field $k_0$ agrees, up to $r$-power multiplications, with one of the prescribed endomorphisms $e\gamma$, the same comparison holds after base change to any ring with no idempotents other than $0$ and $1$. It is used in the construction of a fake elliptic curve with full endomorphism dictionary and height-four formal module, the geometric input on the Čerednik–Drinfeld side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_act_comp_eq_of_isPullbackVia_of_forall_isIdempotentElem_of_closedImmersionBySections_of_isAlgClosed.lean

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_act_comp_eq_of_isPullbackVia_of_forall_isIdempotentElem_of_closedImmersionBySections_of_isAlgClosed
    {r N : ℕ} {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (A₀ : FakeEllipticCurve Λ N k₀)

    (𝓛 : A₀.A.Modules) (h𝓛₁ : Scheme.Modules.IsInvertible 𝓛) (h𝓛₂ : Scheme.Modules.ClosedImmersionBySections 𝓛 A₀.f)

    {a₁ b₁ : ℚ} (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (e e' : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f) (deg : ↥Γt → ℕ)
    (hE1 : ∀ γ : ↥Γt, FakeEllipticCurve.IsIsogenyPair (r ^ deg γ) A₀ A₀ (e γ) (e' γ) ∧ FakeEllipticCurve.PreservesLevel A₀ A₀ (e γ) (he γ))

    (hE4₀ : ∀ (φ ψ : A₀.A ⟶ A₀.A) (d : ℕ) (hφ : φ ≫ A₀.f = A₀.f),
        FakeEllipticCurve.IsIsogenyPair (r ^ d) A₀ A₀ φ ψ → FakeEllipticCurve.PreservesLevel A₀ A₀ φ hφ →
        ∃ (γ : ↥Γt) (i j : ℕ), φ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∀ (Bb : Type) [CommRing Bb] (ψb : k₀ →+* Bb)
      (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A) (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA),
      ∀ (φ ψ : Ab.A ⟶ Ab.A) (d : ℕ) (hφ : φ ≫ Ab.f = Ab.f),
        FakeEllipticCurve.IsIsogenyPair (r ^ d) Ab Ab φ ψ → FakeEllipticCurve.PreservesLevel Ab Ab φ hφ →
        (∀ x : Bb, IsIdempotentElem x → x = 0 ∨ x = 1) →
        ∃ (γ : ↥Γt) (i j : ℕ), φ ≫ Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ gA = gA ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
