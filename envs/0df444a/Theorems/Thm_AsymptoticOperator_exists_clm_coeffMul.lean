-- Prove2me | Theorems.Thm_AsymptoticOperator_exists_clm_coeffMul
-- name    : AsymptoticOperator.exists_clm_coeffMul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T18:26:33.356034+00:00
-- url     : https://prove2.me/theorems/053969ff-544c-42ce-81aa-3dcdeab18cbe
-- title:
--   Multiplication by a continuous matrix loop is a bounded operator on L²(S¹, ℝ²ⁿ)
-- statement:
--   Let $n\ge 0$ and let $S:S^1\to\mathbb R^{2n\times 2n}$ be a continuous loop of real matrices, where $S^1=\mathbb R/\mathbb Z$ carries its Haar probability measure. Then there is a bounded linear operator $B$ on $L^2(S^1,\mathbb R^{2n})$ that is multiplication by $S$, $(Bf)(t)=S(t)f(t)$, in the sense that for every $f\in L^2$ and every $k\in\mathbb Z$
--   $$\widehat{(Bf)}_k=\widehat{(Sf)}_k=\int_{S^1}e^{-2\pi i k t}\,S(t)f(t)\,dt .$$
--
--   Role: the zeroth-order part $f\mapsto Sf$ of the asymptotic operator $A_S=-J_0\partial_t-S$, as an element of $\mathcal L(L^2)$. Reusable wherever $A_S$ is compared with $-J_0\partial_t$ or perturbed by bounded operators.
--
--   Formalization note: $L^2$ is `L2 n`, $\hat f_k$ is `coeff f k` and $\widehat{(Sf)}_k$ is `coeffMul S f k` from the `AsymptoticOperator_Setting` definition module (Fourier coefficients of the complexified functions). Bounded operators are `L2 n →L[ℝ] L2 n`. No symmetry of $S$ is assumed.
-- source:
--   Standard; Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, §3.2, equation (3.4)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- For a continuous loop `S : S¹ → ℝ^{2n×2n}`, multiplication `f ↦ S f`, `(S f)(t) = S(t) f(t)`,
is a bounded linear operator on `L²(S¹, ℝ²ⁿ)`: there is `B ∈ 𝓛(L²)` with
`(B f)^ₖ = (S f)^ₖ` for every `f` and every `k ∈ ℤ`. -/
theorem exists_clm_coeffMul {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    ∃ B : L2 n →L[ℝ] L2 n, ∀ (f : L2 n) (k : ℤ), coeff (B f) k = coeffMul S f k := by sorry

end AsymptoticOperator
