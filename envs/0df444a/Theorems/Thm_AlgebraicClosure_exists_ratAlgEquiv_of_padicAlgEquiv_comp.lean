-- Prove2me | Theorems.Thm_AlgebraicClosure_exists_ratAlgEquiv_of_padicAlgEquiv_comp
-- name    : AlgebraicClosure.exists_ratAlgEquiv_of_padicAlgEquiv_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/4fbf5558-65af-5408-a1b7-8e8613b2ccc0
-- title:
--   Automorphisms of mathbb Qₚ̄ descend along ℚ̄hookrightarrowmathbb Qₚ̄
-- statement:
--   Let $p$ be a prime. Given a $\mathbb Q$-algebra homomorphism $\iota$ from the algebraic closure $\overline{\mathbb Q}$ (Mathlib's `AlgebraicClosure ℚ`) into the algebraic closure $\overline{\mathbb Q_p}$ of the $p$-adic field $\mathbb Q_p$, and given a $\mathbb Q_p$-algebra automorphism $\sigma$ of $\overline{\mathbb Q_p}$, the assertion is that there exists a $\mathbb Q$-algebra automorphism $\sigma'$ of $\overline{\mathbb Q}$ such that $\sigma(\iota(x)) = \iota(\sigma'(x))$ for every $x \in \overline{\mathbb Q}$. Thus $\sigma$ preserves the image of $\iota$ and the induced map on $\overline{\mathbb Q}$ is realised by an element of $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$. The statement is purely existential: no compatibility of the chosen $\sigma'$ with $\sigma$ beyond the displayed intertwining identity is asserted, and in particular no uniqueness claim and no statement that $\sigma \mapsto \sigma'$ is a group homomorphism is made here.
--
--   This is the restriction map from the decomposition group $G_{\mathbb Q_p} = \operatorname{Aut}_{\mathbb Q_p}(\overline{\mathbb Q_p})$ to $G_{\mathbb Q} = \operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ attached to an embedding $\iota\colon \overline{\mathbb Q} \hookrightarrow \overline{\mathbb Q_p}$, stated existentially for one automorphism at a time. It is used in the comparison of torsion points of a Weierstrass curve over $\overline{\mathbb Q}$ with those over $\overline{\mathbb Q_p}$, where a Galois-equivariance statement over $\mathbb Q_p$ must be transported to one over $\mathbb Q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_exists_ratAlgEquiv_of_padicAlgEquiv_comp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicClosure.exists_ratAlgEquiv_of_padicAlgEquiv_comp
    (p : ℕ) [Fact p.Prime]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p])
    (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) :
    ∃ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x : AlgebraicClosure ℚ, σ (ι x) = ι (σ' x) := by sorry
