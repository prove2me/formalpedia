-- Prove2me | Theorems.Thm_AddMonoidHom_IsDualPair_forall_q_zsmul_eq_zero_of_isCoprime
-- name    : AddMonoidHom.IsDualPair.forall_q_zsmul_eq_zero_of_isCoprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/2608227d-f6e6-54eb-8eb4-ced80ed91a52
-- title:
--   Dual pairs of degree coprime to q transport q-torsion-freeness
-- statement:
--   Let $A$ and $B$ be additive abelian groups, let $\varphi : A \to B$ and $\psi : B \to A$ be additive homomorphisms, and let $n$ be an integer such that the pair $(\varphi,\psi)$ satisfies [`AddMonoidHom.IsDualPair φ ψ n`](def/DualIsogenyAPI.html#L9), that is, $\psi(\varphi(a)) = n \cdot a$ for every $a \in A$ and $\varphi(\psi(b)) = n \cdot b$ for every $b \in B$ (integer scalar multiplication). Let $q$ be a natural number whose image in $\mathbb{Z}$ is coprime to $n$ in the Bézout sense, i.e. there are integers $u,v$ with $u n + v q = 1$. Assume $A$ has no nonzero $q$-torsion: every $a \in A$ with $q \cdot a = 0$ is zero. The conclusion is that $B$ likewise has no nonzero $q$-torsion: every $b \in B$ with $q \cdot b = 0$ is zero. No finiteness, topology or further structure on $A$, $B$ is assumed; $q$ is not required to be prime, and $n$ need not be nonzero beyond what coprimality with $q$ forces.
--
--   This is the group-theoretic core of the statement that supersingularity is invariant under isogenies of degree prime to the characteristic: applied to the point groups of elliptic curves with $\varphi$ an isogeny of degree $n$ and $\psi$ its dual, it transports absence of $q$-torsion from the source to the target. It is used in the analysis of fibres of the polynomial attached to points of the modular curve, via [`ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly`](thm.html#ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_IsDualPair_forall_q_zsmul_eq_zero_of_isCoprime.lean

import Mathlib
import Definitions.Def_DualIsogenyAPI

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AddMonoidHom.IsDualPair.forall_q_zsmul_eq_zero_of_isCoprime
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (hdual : AddMonoidHom.IsDualPair φ ψ n) (q : ℕ)
    (hcop : IsCoprime n (q : ℤ))
    (hA : ∀ a : A, (q : ℤ) • a = 0 → a = 0) :
    ∀ b : B, (q : ℤ) • b = 0 → b = 0 := by sorry
