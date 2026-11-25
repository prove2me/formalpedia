-- Prove2me | Theorems.Thm_DetDLP_residual_kronecker_digit_words
-- name    : DetDLP.residual_kronecker_digit_words
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T13:53:37.915795+00:00
-- url     : https://prove2.me/theorems/230646c6-d9b3-49f3-a6a9-8586e1309dbe
-- title:
--   Exact recovery of bivariate residual contractions from scalar output words
-- statement:
--   Consider a Boolean bipartite tensor network with nonnegative integer bivariate polynomial entries of bidegree below $(\kappa,\ell)$ and coefficients below $2^{hJ}$. Split each vertex entry into base-$2^h$ digits. For every tuple of digit choices, pack the exponents $(i,j)$ as $i+Kj$ with $K=|V|(\kappa-1)+1$, reduce modulo $2^P$, and truncate at $K\ell$. Here $P=\beta+|V|h+|V|\lceil\log_2(\kappa\ell)\rceil+2$ and $|E|\le\beta$. Given canonical binary words encoding those scalar contractions, the weighted sum of their decoded coefficients gives each exact integer coefficient of the original contraction through terminal degree $\ell-1$.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.3, complete algebraic reduction of the residual network to binary-encoded scalar outputs.

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

open Polynomial Finset

namespace DetDLP

theorem residual_kronecker_digit_words (G : BipartiteMultigraph) (κ ℓ J h β : ℕ) (he : G.nE ≤ β)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin (κ*ℓ) → ℕ)
    (hA : ∀ v t s,A v t s < 2^(h*J)) :
    let K := G.nV*(κ-1)+1
    let P := β+G.nV*h+G.nV*Nat.clog 2 (κ*ℓ)+2
    let L := K*ℓ
    let coord := (finProdFinEquiv (m:=κ) (n:=ℓ)).symm
    let full (v : Fin G.nV) (t : Fin (G.deg v) → Bool) : Polynomial (Polynomial ℤ) :=
      ∑ s, monomial (coord s).2.val (monomial (coord s).1.val ((A v t s):ℤ))
    let slice (a : Fin G.nV → Fin J) (v : Fin G.nV) (t : Fin (G.deg v) → Bool) : Polynomial (ZMod (2^P)) :=
      ∑ s, monomial ((coord s).1.val+K*(coord s).2.val)
        (((A v t s / 2^(h*(a v).val) % 2^h):ℕ):ZMod (2^P))
    ∀ w : (Fin G.nV → Fin J) → List Bool,
      (∀ a,EncodesTruncPoly P L (w a) (BTNContract G (fun v t => Ideal.Quotient.mk _ (slice a v t)))) →
      ∃ c : (Fin G.nV → Fin J) → Fin L → ℕ,
        (∀ a,w a=encodeNatListBin (List.ofFn (c a))) ∧ (∀ a i,c a i < 2^P) ∧
        ∀ i : Fin K, ∀ j : Fin ℓ,
          ((BTNContract G full).coeff j.val).coeff i.val =
            ∑ a : Fin G.nV → Fin J, (2:ℤ)^(h*∑ v,(a v).val) *
              ((c a ⟨i.val+K*j.val,by
                have H := Nat.mul_le_mul_left K j.isLt
                rw [Nat.mul_succ] at H; have := i.isLt; omega⟩):ℤ) := by sorry

end DetDLP
