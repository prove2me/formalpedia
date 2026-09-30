-- Prove2me | Theorems.Thm_BurauFaithful_sl2_descent_word
-- name    : BurauFaithful.sl2_descent_word
-- status  : Open
-- author  : @lt9
-- created : 2026-09-30T11:25:12.52822+00:00
-- url     : https://prove2.me/theorems/40e4979f-781b-4e1e-85ee-1a2723a2dd97
-- title:
--   The Euclidean descent in $\mathrm{SL}(2,\mathbb Z)$ produces an explicit word in $S$ and $T$
-- statement:
--   The Euclidean algorithm in the modular group, expressed as a *word in the generators*.
--
--   Let $S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$ and $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ be the standard generators of $\mathrm{SL}(2,\mathbb Z)$, and let $M$ be an integral $2\times2$ matrix of determinant $1$. One step of the Euclidean descent replaces $M$ by
--   $$N=\bigl(M\cdot T^{\,n}\bigr)\cdot S,\qquad n=-\Bigl\lfloor\frac{M_{01}}{M_{00}}\Bigr\rfloor ,$$
--   which strictly decreases $|M_{00}|$; the descent terminates when $M_{00}=0$, where $M=\pm S\,T^{k}$.
--
--   The theorem states that the descent produces an explicit finite list of matrices, each equal to $S$, to $S^{-1}=S^{3}$ or to a power of $T$, whose product is exactly $M$:
--   $$\exists\,\ell,\qquad \prod_{i<\ell} W_i \;=\; M,\qquad W_i\in\{S,S^{3}\}\cup\{T^{n}:n\in\mathbb Z\},$$
--   namely the canonical word attached to $M$ by the descent (the continued fraction expansion of $M$).
--
--   This is the object on which the two multiplication rules of the descent section are stated — right multiplication by $T^{j}$ shifts the recorded exponent, and right multiplication by $S$ is the continued fraction reciprocity — and those rules make the section multiplicative, yielding $\ker(\rho_3|_{t=-1})=\langle\Delta^4\rangle$ and hence the faithfulness theorem for three strands (Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, §3.3, pp. 129–130).
--
--   **Formalization Note** The descent is implemented as a structural recursion on a step budget (`iterWord`), with `word M = iterWord (M 0 0).natAbs M`; correctness is proved by induction on the budget, the base case being the terminal classification of a unimodular matrix with vanishing top-left entry.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, §3.3, pp. 129-130; C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups*, 2nd ed., Springer 1964, p. 85.

/-
`BurauFaithful.sl2_descent_word`: the Euclidean descent, as a *word in the generators* `S`, `S⁻¹`
and powers of `T`.

`BurauFaithful.sl2_euclid_step` decreases `|M 0 0|` by replacing `M` with `(M · T^n) · S`,
`n = -(M 0 1 / M 0 0)`, and `BurauFaithful.sl2_normal_form_base` describes the terminal case
`M 0 0 = 0` (`M = ±S·T^k`). Iterating gives a list of matrices, each a power of `T` or `S^{±1}`,
whose product is `M`.

The statement proved here is `(word M).prod = M` for every unimodular `M`; this is the object on
which the two multiplication rules of NOTES_BURAU.md (SESSION 14) are stated.

Implementation: structural recursion `iterWord : ℕ → M2 → List M2` on a step budget, then
`word M = iterWord (M 0 0).natAbs M`; the measure strictly decreases at every step, so the budget
suffices (proved by induction on the budget). `simp only [BurauDescent.iterWord, ...]` is the
unfolding idiom (a `rw` does not use the generated equations).
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

namespace BurauDescent

abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ

/-- `S = !![0,-1;1,0]`. -/
def Sm : M2 := !![0, -1; 1, 0]

/-- `T^n = !![1,n;0,1]`. -/
def Tm (n : ℤ) : M2 := !![1, n; 0, 1]

/-- `S⁻¹ = S³`. -/
def Sinv : M2 := Sm * Sm * Sm

/-- Generator word for the terminal case `M 0 0 = 0`: `M = S·T^{M 1 1}` when `M 0 1 = -1`, and
`M = S³·T^{-M 1 1}` otherwise. -/
noncomputable def baseWord (M : M2) : List M2 :=
  if M 0 1 = -1 then [Sm, Tm (M 1 1)] else [Sm, Sm, Sm, Tm (-(M 1 1))]

/-- `k` steps of the Euclidean descent from `M`, followed by the terminal word. -/
noncomputable def iterWord : ℕ → M2 → List M2
  | 0, M => baseWord M
  | k + 1, M =>
      if M 0 0 = 0 then baseWord M
      else iterWord k ((M * Tm (-(M 0 1 / M 0 0))) * Sm) ++ [Sinv, Tm (M 0 1 / M 0 0)]

/-- The Euclidean descent word of `M`. -/
noncomputable def word (M : M2) : List M2 := iterWord (M 0 0).natAbs M

end BurauDescent

theorem BurauFaithful.sl2_descent_word (M : BurauDescent.M2) (hd : M.det = 1) :
    (BurauDescent.word M).prod = M := by sorry
