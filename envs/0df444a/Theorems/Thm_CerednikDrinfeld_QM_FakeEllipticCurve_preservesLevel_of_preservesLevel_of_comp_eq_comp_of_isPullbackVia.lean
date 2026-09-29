-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_preservesLevel_of_comp_eq_comp_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_preservesLevel_of_comp_eq_comp_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/f84bba1a-86af-5dc0-9f78-50dc70e0cdf1
-- title:
--   Level preservation descends along pull-backs of fake elliptic curves
-- statement:
--   Fix $N \in \mathbb{N}$, rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and let $A_0$ be a fake elliptic curve with $\Lambda$-action and level-$N$ structure over a field $k_0$, in the sense of the structure `FakeEllipticCurve` (an abelian scheme $A_0.f : A_0.A \to \operatorname{Spec} k_0$ with a relative group law, commutativity, the smooth–proper–connected-fibre bundle, two-dimensional fibres, a $\Lambda$-action by endomorphisms over the base, and a level scheme $A_0.C$ with its closed immersion $A_0.\mathrm{lev}$). Let $B$ be a nontrivial commutative ring, $\psi : k_0 \to B$ a ring homomorphism, $A_b$ a fake elliptic curve over $B$ for the same $\Lambda$ and $N$, and $g_A : A_b.A \to A_0.A$ a morphism exhibiting $A_b$ as the pull-back of $A_0$ along $\psi$ in the sense of `IsPullbackVia`: the square formed by $g_A$, $A_b.f$, $A_0.f$ and $\operatorname{Spec}(\psi)$ is cartesian, composition with $g_A$ is compatible with the two relative group laws, $A_b.\mathrm{act}(x)$ followed by $g_A$ equals $g_A$ followed by $A_0.\mathrm{act}(x)$ for every $x \in \Lambda$, and every point of $A_b$ factoring through $A_b.\mathrm{lev}$ has its image under $g_A$ factoring through $A_0.\mathrm{lev}$. Let further $\varphi : A_b.A \to A_b.A$ and $\varphi_0 : A_0.A \to A_0.A$ be endomorphisms over their respective bases ($\varphi$ followed by $A_b.f$ equals $A_b.f$, and likewise for $\varphi_0$), satisfying $\varphi$ followed by $g_A$ equals $g_A$ followed by $\varphi_0$. The hypothesis is that $\varphi$ preserves the level structure of $A_b$: for every scheme $T$, every $t' : T \to \operatorname{Spec} B$ and every $T$-point $P$ of $A_b$ over $t'$ which factors through $A_b.\mathrm{lev}$, the composite $P$ followed by $\varphi$ again factors through $A_b.\mathrm{lev}$. The conclusion is the same statement for $A_0$ and $\varphi_0$: every $T$-point of $A_0$ over any $t : T \to \operatorname{Spec} k_0$ factoring through $A_0.\mathrm{lev}$ has its composite with $\varphi_0$ factoring through $A_0.\mathrm{lev}$.
--
--   This is a descent step for level structures: an endomorphism of a fake elliptic curve over a field which preserves the level structure after base change to a nonzero ring already preserves it over the field. It is used in the construction of idempotent-cut endomorphisms compatible with the $\Lambda$-action on fake elliptic curves in the Čerednik–Drinfeld part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_preservesLevel_of_comp_eq_comp_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_preservesLevel_of_comp_eq_comp_of_isPullbackVia
    {N : ℕ} {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {k₀ : Type} [Field k₀] (A₀ : FakeEllipticCurve Λ N k₀)
    {Bb : Type} [CommRing Bb] [Nontrivial Bb] (ψb : k₀ →+* Bb)
    (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A) (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA)
    (φ : Ab.A ⟶ Ab.A) (hφ : φ ≫ Ab.f = Ab.f) (φ₀ : A₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = A₀.f)
    (hφg : φ ≫ gA = gA ≫ φ₀)
    (hlev : FakeEllipticCurve.PreservesLevel Ab Ab φ hφ) :
    FakeEllipticCurve.PreservesLevel A₀ A₀ φ₀ hφ₀ := by sorry
