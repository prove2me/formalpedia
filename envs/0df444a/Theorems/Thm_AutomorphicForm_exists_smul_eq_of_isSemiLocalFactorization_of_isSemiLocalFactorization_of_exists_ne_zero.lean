-- Prove2me | Theorems.Thm_AutomorphicForm_exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero
-- name    : AutomorphicForm.exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/b0f8bb77-b88a-501d-b0d0-9e12a1403e07
-- title:
--   Semi-local factors of a non-zero test function are unique up to scalars
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $S$ be a finite set of finite places of $K$ (height-one primes of $\mathcal{O}_K$), and let $\varphi : \mathrm{GL}_2(\mathbb{A}_{L}) \to \mathbb{C}$ be a function on the points of $\mathrm{GL}_2$ over the adele ring of $L$. Suppose $\varphi$ admits two semi-local factorisations at $S$, given by data $(\varphi_a,\varphi_f,(\varphi_v)_v)$ and $(\varphi_a',\varphi_f',(\varphi_v')_v)$, where each archimedean factor is a function on $\mathrm{GL}_2$ of the infinite adele ring of $L$, each finite factor a function on $\mathrm{GL}_2$ of the finite adele ring, and each semi-local factor indexed by $v$ a function on $\mathrm{GL}_2(L \otimes_K K_v)$; that is, in each case: the archimedean factor is compactly supported and obtained by evaluating a function on $2\times 2$ matrices over the mixed space of $L$ that is $C^\infty$ over $\mathbb{R}$ at the archimedean matrix entries of its argument; the finite factor is locally constant with compact support; each $\varphi_v$ with $v \in S$ is locally constant with compact support; the finite factor of $h$ equals $\prod_{v \in S} \varphi_v$ evaluated at the semi-local components of $h$ whenever all semi-local components of $h$ at places outside $S$ lie in the semi-local integral units set, and vanishes as soon as some component outside $S$ fails to lie there; and $\varphi(g)$ is the product of the archimedean factor at the archimedean part of $g$ with the finite factor at the finite part of $g$. Suppose further that $\varphi$ is not identically zero. Then there exist a scalar $c_a \in \mathbb{C}$ and a function $c$ on height-one primes of $\mathcal{O}_K$ with $c_a \neq 0$, $c(v) \neq 0$ for all $v \in S$, $c_a \prod_{v \in S} c(v) = 1$, $\varphi_a' = c_a \varphi_a$, and $\varphi_v' = c(v)\,\varphi_v$ for every $v \in S$. No assertion is made relating $\varphi_f'$ to $\varphi_f$, nor about the values of $c$ outside $S$.
--
--   This is the uniqueness statement for factorisations of a non-zero factorisable test function on $\mathrm{GL}_2$ over the adeles of $L$, semi-local at a finite set $S$ of places of the base field $K$: the archimedean and semi-local factors are determined up to non-zero scalars whose product is $1$. It is used to normalise the factors in the comparison of hyperbolic terms and in the construction of matching semi-local test data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

open scoped TensorProduct in

theorem AutomorphicForm.exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (φa' : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ' : AutomorphicForm.IsSemiLocalFactorization K L S φ φa' φf' φS')
    (h0 : ∃ g, φ g ≠ 0) :
    ∃ (ca : ℂ) (c : HeightOneSpectrum (𝓞 K) → ℂ),
      ca ≠ 0 ∧ (∀ v ∈ S, c v ≠ 0) ∧ ca * ∏ v ∈ S, c v = 1 ∧
      φa' = ca • φa ∧ ∀ v ∈ S, φS' v = c v • φS v := by sorry
