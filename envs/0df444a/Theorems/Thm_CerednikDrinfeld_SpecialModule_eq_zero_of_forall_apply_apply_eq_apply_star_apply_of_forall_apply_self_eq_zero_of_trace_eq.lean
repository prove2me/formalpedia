-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialModule_eq_zero_of_forall_apply_apply_eq_apply_star_apply_of_forall_apply_self_eq_zero_of_trace_eq
-- name    : CerednikDrinfeld.SpecialModule.eq_zero_of_forall_apply_apply_eq_apply_star_apply_of_forall_apply_self_eq_zero_of_trace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/64f71426-7e87-5653-88a6-1174239c4357
-- title:
--   Vanishing of alternating ⋆-balanced forms at a ramified prime
-- statement:
--   Let $q \neq q'$ be primes and $a, b \in \mathbb{Q}$ be such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q}, a, b]$ satisfies $0 < a$ or $0 < b$ and, for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the algebra $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and is the largest submodule with these four properties among those containing it. Let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq') \cdot 1$, and let $\mathrm{star} \colon \Lambda \to \Lambda$ be any function with $\mu \cdot \mathrm{star}(x) = \bar{x} \mu$ for all $x \in \Lambda$, where $\bar{\;\cdot\;}$ is quaternionic conjugation. Let $p$ be a prime equal to $q$ or to $q'$, let $k$ be an algebraically closed field of characteristic $p$, and let $W$ be a finite-dimensional $k$-vector space with $\dim_k W = 2$. Let $\Psi \colon \Lambda \to \mathrm{End}_k(W)$ be additive, send $1 \in \Lambda$ to the identity, and satisfy $\Psi(xy) = \Psi(x) \circ \Psi(y)$ for $x, y \in \Lambda$ with $xy \in \Lambda$, and assume the trace condition: whenever $m \in \Lambda$ and $n \in \mathbb{Z}$ satisfy $m + \bar{m} = n$, one has $\mathrm{tr}_k(\Psi(m)) = n$ in $k$. Finally let $\mathrm{bf} \colon W \times W \to k$ be $k$-bilinear with $\mathrm{bf}(v, \Psi(x) w) = \mathrm{bf}(\Psi(\mathrm{star}(x)) v, w)$ for all $x \in \Lambda$ and $v, w \in W$, and with $\mathrm{bf}(v, v) = 0$ for all $v$. Then $\mathrm{bf} = 0$.
--
--   This is the local vanishing statement at a prime dividing the discriminant of the quaternion algebra: a two-dimensional representation of a maximal order in characteristic $p \mid qq'$ satisfying Drinfeld's trace normalisation admits no nonzero alternating $\star$-balanced pairing. It is the pointwise input to [`CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isRamified`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isRamified), where $W$ is the dual of a one-dimensional piece of the tangent or Tate module of a fake elliptic curve and the pairing comes from an alternating tensor; the proof cites [`QuaternionAlgebra.IsMaximalOrder.exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq) for the existence of a suitable element $\omega \in \Lambda$ with prescribed reduced trace and norm and irreducible characteristic polynomial modulo $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialModule_eq_zero_of_forall_apply_apply_eq_apply_star_apply_of_forall_apply_self_eq_zero_of_trace_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.SpecialModule.eq_zero_of_forall_apply_apply_eq_apply_star_apply_of_forall_apply_self_eq_zero_of_trace_eq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {p : ℕ} [Fact p.Prime] (hp : p = q ∨ p = q')
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (W : Type) [AddCommGroup W] [Module k W] [Module.Finite k W] (hW : Module.finrank k W = 2)
    (Ψ : ↥Λ → (W →ₗ[k] W))
    (hΨ_add : ∀ x y : ↥Λ, Ψ (x + y) = Ψ x + Ψ y)
    (hΨ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, Ψ ⟨1, h1⟩ = LinearMap.id)
    (hΨ_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      Ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = Ψ x ∘ₗ Ψ y)
    (htr : ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + Star.star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
      LinearMap.trace k W (Ψ m) = (n : k))
    (bf : W →ₗ[k] W →ₗ[k] k)
    (hbal : ∀ (x : ↥Λ) (v w : W), bf v (Ψ x w) = bf (Ψ (star x) v) w)
    (halt : ∀ v : W, bf v v = 0) :
    bf = 0 := by sorry
