-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre
-- name    : AlgebraicCurve.exists_local_coboundary_of_smallExtension_of_monogenic_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/5f88db1d-07aa-5927-94b2-0ae1d36dac87
-- title:
--   Local vanishing of the associativity obstruction for monogenic fibres
-- statement:
--   Let $K$ be a field, $n$ a natural number, and $B$ a commutative $K[X]$-algebra admitting a $K[X]$-basis $b_0,\dots,b_n$ with $b_0=1$; write $b.\mathrm{repr}(b_ib_j)_k\in K[X]$ for the coordinates of the products. Let $\pi\colon A'\to A$ be a surjective homomorphism of commutative rings and $\varepsilon\in A'$ an element with $\pi a=0\iff\varepsilon\mid a$, let $\rho\colon A\to K$ be surjective, and assume $\varepsilon a=0$ implies $\rho(\pi a)=0$. Let $\gamma_{ijk}\in A[X]$ satisfy $\gamma_{0jk}=\delta_{jk}$, the symmetry $\gamma_{ijk}=\gamma_{jik}$, the associativity relations $\sum_k\gamma_{ijk}\gamma_{klm}=\sum_k\gamma_{jlk}\gamma_{ikm}$, and reduce coefficientwise under $\rho$ to the structure constants $b.\mathrm{repr}(b_ib_j)_k$. Let $\gamma'_{ijk}\in A'[X]$ be unital ($\gamma'_{0jk}=\delta_{jk}$) and symmetric with $\pi$-reduction $\gamma_{ijk}$, and let $ac_{ijlm}\in A'[X]$ satisfy $\sum_k\gamma'_{ijk}\gamma'_{klm}-\sum_k\gamma'_{jlk}\gamma'_{ikm}=\varepsilon\,ac_{ijlm}$. Let $P\subset K[X]$ be a maximal ideal and suppose there is $y\in B$ such that every $z\in B$ lies, modulo $P\cdot B$, in the image of $q\mapsto q(y)$ for $q\in K[X][X]$. Then there exist $s\in K[X]$ with $s\notin P$ and a family $\varphi_{ijk}\in K[X]$ with $\varphi_{0jk}=0$ and $\varphi_{ijk}=\varphi_{jik}$ such that, for all $i,j,l,m$, $$\sum_k\varphi_{jlk}\,b.\mathrm{repr}(b_ib_k)_m-\sum_k b.\mathrm{repr}(b_ib_j)_k\,\varphi_{klm}+\sum_k b.\mathrm{repr}(b_jb_l)_k\,\varphi_{ikm}-\sum_k\varphi_{ijk}\,b.\mathrm{repr}(b_kb_l)_m=s\cdot (ac_{ijlm})^{\rho\circ\pi},$$ where the superscript denotes coefficientwise application of $\rho\circ\pi$.
--
--   This is the local statement that the Hochschild-type obstruction cochain $ac$ to lifting the structure constants $\gamma$ along the small extension $\pi\colon A'\to A$ becomes a coboundary after inverting one element outside $P$, the input being monogenicity of the fibre of $B$ at $P$; the liftability is obtained from [`Algebra.exists_lift_basis_of_surjective_of_monogenic_specialFibre`](thm.html#Algebra.exists_lift_basis_of_surjective_of_monogenic_specialFibre). It feeds the corresponding statement at infinity and the global construction of lifted structure constants in normal form, via [`AlgebraicCurve.exists_coboundary_at_infinity_of_smallExtension_of_split`](thm.html#AlgebraicCurve.exists_coboundary_at_infinity_of_smallExtension_of_split) and [`AlgebraicCurve.exists_lift_normalForm_structureConstants_of_smallExtension`](thm.html#AlgebraicCurve.exists_lift_normalForm_structureConstants_of_smallExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

universe u v w w'

theorem AlgebraicCurve.exists_local_coboundary_of_smallExtension_of_monogenic_fibre
    (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [Algebra K[X] B]
    (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0)
    (hγ'c : ∀ i j k, γ' i j k = γ' j i k)
    (hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k)
    (ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      Polynomial.C ε * ac i j l m)
    (P : Ideal K[X]) (hP : P.IsMaximal)
    (hmono : ∃ y : B, ∀ z : B, ∃ q : Polynomial K[X],
      z - aeval y q ∈ P • (⊤ : Submodule K[X] B)) :
    ∃ s : K[X], s ∉ P ∧ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      ∀ i j l m, (∑ k, φ j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * φ k l m) +
          (∑ k, b.repr (b j * b l) k * φ i k m) - (∑ k, φ i j k * b.repr (b k * b l) m) =
        s * (ac i j l m).map (ρ.comp π) := by sorry
