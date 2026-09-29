-- Prove2me | Theorems.Thm_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero
-- name    : Deformation.exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/ac508dfe-38d7-5dd5-ae25-063a0160e589
-- title:
--   First Witt coordinates of homomorphisms into Wₙ₊₁
-- statement:
--   Let $k$ be a perfect field of characteristic $p$, with $p$ prime, let $n$ be a natural number, and let $A$ be a commutative ring carrying the structure of a Hopf algebra over $k$ which is finite-dimensional as a $k$-module and cocommutative. Write $A^{*} = \operatorname{Hom}_{k}(A,k)$ for the dual, equipped with the convolution product (the type `WithConv (A →ₗ[k] k)`, with `ofConv` the underlying functional and powers taken convolutionally). Assume that every $\beta \in A^{*}$ with $\beta(1)=0$ satisfies $\beta^{p^{n+1}}=0$. Then for $x_{0} \in A$ the following are equivalent. First, there is a truncated Witt vector $x$ of length $n+1$ with coordinates in $A$ lying in [`Deformation.wittHom`](def/Dieudonne_WittVectorHom.html#L246), that is, satisfying $W_{n+1}(\Delta)(x) = W_{n+1}(\iota_{1})(x) + W_{n+1}(\iota_{2})(x)$ in $W_{n+1}(A \otimes_{k} A)$, where $\Delta$ is the comultiplication and $\iota_{1},\iota_{2}$ the two inclusions $A \to A \otimes_{k} A$, and with $x$ having $0$-th coordinate $x_{0}$. Second, $x_{0}$ lies in [`primitives k A`](def/Dieudonne_ModpRealization.html#L16), the kernel of $\Delta - (\,\cdot\, \otimes 1) - (1 \otimes \,\cdot\,)$, and there exists $a \in A$ with $\beta(x_{0})^{p^{n}} = \beta^{p^{n}}(a)$ for every $\beta \in A^{*}$.
--
--   In Dieudonné-theoretic terms this identifies the additive characters of a finite commutative group scheme $G = \operatorname{Spec} A$ killed by $V^{n+1}$ (in dual form, the hypothesis on convolution powers) that extend to homomorphisms $G \to W_{n+1}$: those primitive $x_{0}$ whose $p^{n}$-th Frobenius twist factors through the image of the $n$-th Verschiebung. It is used in the proof of [`HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero`](thm.html#HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ (n + 1) = 0)
    (x₀ : A) :
    (∃ x : TruncatedWittVector p (n + 1) A,
        x ∈ Deformation.wittHom k p (n + 1) A ∧ x.coeff 0 = x₀) ↔
      (x₀ ∈ primitives k A ∧
        ∃ a : A, ∀ β : WithConv (A →ₗ[k] k),
          (β.ofConv x₀) ^ p ^ n = (β ^ p ^ n).ofConv a) := by sorry
