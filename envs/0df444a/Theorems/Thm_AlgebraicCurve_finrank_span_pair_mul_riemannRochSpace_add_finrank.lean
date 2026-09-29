-- Prove2me | Theorems.Thm_AlgebraicCurve_finrank_span_pair_mul_riemannRochSpace_add_finrank
-- name    : AlgebraicCurve.finrank_span_pair_mul_riemannRochSpace_add_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/d3cfa6a0-7216-5879-adcf-b5cfcea108b7
-- title:
--   Base-point-free pencil trick for Riemann–Roch spaces
-- statement:
--   Let $K \subseteq F$ be fields, $F$ a $K$-algebra, and work with the places of $F$ over $K$ in the project's sense: valuation subrings of $F$ containing $\operatorname{im}(K \to F)$, distinct from $F$ itself, and principal ideal rings; each place $w$ carries its adic valuation and the integer-valued order function $\operatorname{ord}_w f = -\log w(f)$. A divisor is a finitely supported function from places to $\mathbb{Z}$, and for a divisor $D$ the space $L(D)$ (`riemannRochSpace D`) is the $K$-submodule of $f \in F$ with $w(f) \le \exp(D\,w)$ at every place $w$, i.e. $\operatorname{ord}_w f \ge -D\,w$ for $f \neq 0$. Given divisors $L, M$ and nonzero $f_1, f_2 \in F$ such that $\operatorname{ord}_w f_1 + L\,w \ge 0$ and $\operatorname{ord}_w f_2 + L\,w \ge 0$ for every place $w$, and such that at every place $w$ at least one of $\operatorname{ord}_w f_1 + L\,w$, $\operatorname{ord}_w f_2 + L\,w$ vanishes, and assuming $L(M)$ finite-dimensional over $K$, the theorem asserts two things: first, the dimension identity $\dim_K\big(\langle f_1,f_2\rangle \cdot L(M)\big) + \dim_K L(M-L) = 2\dim_K L(M)$, where $\langle f_1,f_2\rangle \cdot L(M)$ is the product of the $K$-span of $\{f_1,f_2\}$ with $L(M)$ as submodules of $F$; second, the inclusion $\langle f_1,f_2\rangle \cdot L(M) \subseteq L(M+L)$.
--
--   This is Castelnuovo's base-point-free pencil trick expressed for Riemann–Roch spaces of divisors on a function field, the hypotheses on $f_1, f_2$ saying that they are nonzero sections of $L$ with no common zero. It is used downstream in computations with Riemann–Roch spaces on the modular curve, in particular for the identities concerning the divisor attached to an embedding.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrank_span_pair_mul_riemannRochSpace_add_finrank.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.finrank_span_pair_mul_riemannRochSpace_add_finrank
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (L M : AlgebraicCurve.Divisor K F) {f₁ f₂ : F} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (h₁ : ∀ w : AlgebraicCurve.Place K F, 0 ≤ w.ord f₁ + L w)
    (h₂ : ∀ w : AlgebraicCurve.Place K F, 0 ≤ w.ord f₂ + L w)
    (hbpf : ∀ w : AlgebraicCurve.Place K F, w.ord f₁ + L w = 0 ∨ w.ord f₂ + L w = 0)
    [FiniteDimensional K ↥(AlgebraicCurve.riemannRochSpace M)] :
    Module.finrank K ↥(Submodule.span K {f₁, f₂} * AlgebraicCurve.riemannRochSpace M)
        + Module.finrank K ↥(AlgebraicCurve.riemannRochSpace (M - L))
      = 2 * Module.finrank K ↥(AlgebraicCurve.riemannRochSpace M) ∧
    Submodule.span K {f₁, f₂} * AlgebraicCurve.riemannRochSpace M ≤ AlgebraicCurve.riemannRochSpace (M + L) := by sorry
